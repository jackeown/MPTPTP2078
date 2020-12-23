%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:34 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  146 (1334 expanded)
%              Number of clauses        :   89 ( 376 expanded)
%              Number of leaves         :   18 ( 343 expanded)
%              Depth                    :   20
%              Number of atoms          :  387 (6287 expanded)
%              Number of equality atoms :  156 (1318 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK1
        & v3_tops_1(sK1,X0)
        & v3_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f35,f34])).

fof(f56,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) )
            & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f40,f40])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f58,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0)
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_252,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_254,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_252,c_19,c_18])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_938,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_254,c_739])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_833,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_834,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_1440,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_938,c_23,c_834])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_749,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1647,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_1440,c_749])).

cnf(c_748,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_359,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_360,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_743,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_1370,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_743])).

cnf(c_14,plain,
    ( v2_tops_1(X0,X1)
    | ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_16,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_324,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_325,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_840,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_1387,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1370,c_19,c_18,c_325,c_840])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_740,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_1020,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_748,c_740])).

cnf(c_1390,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1387,c_1020])).

cnf(c_1903,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1647,c_1390])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1905,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1903,c_2])).

cnf(c_1445,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_743])).

cnf(c_6,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_313,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_314,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_837,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_1958,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_19,c_18,c_314,c_833,c_837])).

cnf(c_1961,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1958,c_254])).

cnf(c_2126,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1905,c_1961])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_741,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_943,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_748,c_741])).

cnf(c_1391,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1387,c_943])).

cnf(c_1645,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_748,c_749])).

cnf(c_1662,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1391,c_1645])).

cnf(c_2129,plain,
    ( k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2126,c_1662])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X0) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_200,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X0) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_201,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X0) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(X0,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X0) = k2_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_201,c_19])).

cnf(c_206,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X0) = k2_tops_1(sK0,X0) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X0) = k2_tops_1(sK0,X0)
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_206])).

cnf(c_281,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_283,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_281,c_18])).

cnf(c_1726,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1647,c_283])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1805,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_1726,c_0])).

cnf(c_1965,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0))) = k4_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1961,c_1805])).

cnf(c_2176,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_1965,c_2126])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_760,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_2])).

cnf(c_2177,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2176,c_760])).

cnf(c_2180,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2129,c_2177])).

cnf(c_530,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_854,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_1907,plain,
    ( sK1 != k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_1767,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(sK1,k1_xboole_0)
    | k4_xboole_0(sK1,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_1768,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1767])).

cnf(c_902,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_1083,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_1338,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != sK1
    | sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_529,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_910,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_904,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_550,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2180,c_1907,c_1768,c_1338,c_910,c_904,c_550,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.49/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/0.99  
% 2.49/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/0.99  
% 2.49/0.99  ------  iProver source info
% 2.49/0.99  
% 2.49/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.49/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/0.99  git: non_committed_changes: false
% 2.49/0.99  git: last_make_outside_of_git: false
% 2.49/0.99  
% 2.49/0.99  ------ 
% 2.49/0.99  
% 2.49/0.99  ------ Input Options
% 2.49/0.99  
% 2.49/0.99  --out_options                           all
% 2.49/0.99  --tptp_safe_out                         true
% 2.49/0.99  --problem_path                          ""
% 2.49/0.99  --include_path                          ""
% 2.49/0.99  --clausifier                            res/vclausify_rel
% 2.49/0.99  --clausifier_options                    --mode clausify
% 2.49/0.99  --stdin                                 false
% 2.49/0.99  --stats_out                             all
% 2.49/0.99  
% 2.49/0.99  ------ General Options
% 2.49/0.99  
% 2.49/0.99  --fof                                   false
% 2.49/0.99  --time_out_real                         305.
% 2.49/0.99  --time_out_virtual                      -1.
% 2.49/0.99  --symbol_type_check                     false
% 2.49/0.99  --clausify_out                          false
% 2.49/0.99  --sig_cnt_out                           false
% 2.49/0.99  --trig_cnt_out                          false
% 2.49/0.99  --trig_cnt_out_tolerance                1.
% 2.49/0.99  --trig_cnt_out_sk_spl                   false
% 2.49/0.99  --abstr_cl_out                          false
% 2.49/0.99  
% 2.49/0.99  ------ Global Options
% 2.49/0.99  
% 2.49/0.99  --schedule                              default
% 2.49/0.99  --add_important_lit                     false
% 2.49/0.99  --prop_solver_per_cl                    1000
% 2.49/0.99  --min_unsat_core                        false
% 2.49/0.99  --soft_assumptions                      false
% 2.49/0.99  --soft_lemma_size                       3
% 2.49/0.99  --prop_impl_unit_size                   0
% 2.49/0.99  --prop_impl_unit                        []
% 2.49/0.99  --share_sel_clauses                     true
% 2.49/0.99  --reset_solvers                         false
% 2.49/0.99  --bc_imp_inh                            [conj_cone]
% 2.49/0.99  --conj_cone_tolerance                   3.
% 2.49/0.99  --extra_neg_conj                        none
% 2.49/0.99  --large_theory_mode                     true
% 2.49/0.99  --prolific_symb_bound                   200
% 2.49/0.99  --lt_threshold                          2000
% 2.49/0.99  --clause_weak_htbl                      true
% 2.49/0.99  --gc_record_bc_elim                     false
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing Options
% 2.49/0.99  
% 2.49/0.99  --preprocessing_flag                    true
% 2.49/0.99  --time_out_prep_mult                    0.1
% 2.49/0.99  --splitting_mode                        input
% 2.49/0.99  --splitting_grd                         true
% 2.49/0.99  --splitting_cvd                         false
% 2.49/0.99  --splitting_cvd_svl                     false
% 2.49/0.99  --splitting_nvd                         32
% 2.49/0.99  --sub_typing                            true
% 2.49/0.99  --prep_gs_sim                           true
% 2.49/0.99  --prep_unflatten                        true
% 2.49/0.99  --prep_res_sim                          true
% 2.49/0.99  --prep_upred                            true
% 2.49/0.99  --prep_sem_filter                       exhaustive
% 2.49/0.99  --prep_sem_filter_out                   false
% 2.49/0.99  --pred_elim                             true
% 2.49/0.99  --res_sim_input                         true
% 2.49/0.99  --eq_ax_congr_red                       true
% 2.49/0.99  --pure_diseq_elim                       true
% 2.49/0.99  --brand_transform                       false
% 2.49/0.99  --non_eq_to_eq                          false
% 2.49/0.99  --prep_def_merge                        true
% 2.49/0.99  --prep_def_merge_prop_impl              false
% 2.49/0.99  --prep_def_merge_mbd                    true
% 2.49/0.99  --prep_def_merge_tr_red                 false
% 2.49/0.99  --prep_def_merge_tr_cl                  false
% 2.49/0.99  --smt_preprocessing                     true
% 2.49/0.99  --smt_ac_axioms                         fast
% 2.49/0.99  --preprocessed_out                      false
% 2.49/0.99  --preprocessed_stats                    false
% 2.49/0.99  
% 2.49/0.99  ------ Abstraction refinement Options
% 2.49/0.99  
% 2.49/0.99  --abstr_ref                             []
% 2.49/0.99  --abstr_ref_prep                        false
% 2.49/0.99  --abstr_ref_until_sat                   false
% 2.49/0.99  --abstr_ref_sig_restrict                funpre
% 2.49/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/0.99  --abstr_ref_under                       []
% 2.49/0.99  
% 2.49/0.99  ------ SAT Options
% 2.49/0.99  
% 2.49/0.99  --sat_mode                              false
% 2.49/0.99  --sat_fm_restart_options                ""
% 2.49/0.99  --sat_gr_def                            false
% 2.49/0.99  --sat_epr_types                         true
% 2.49/0.99  --sat_non_cyclic_types                  false
% 2.49/0.99  --sat_finite_models                     false
% 2.49/0.99  --sat_fm_lemmas                         false
% 2.49/0.99  --sat_fm_prep                           false
% 2.49/0.99  --sat_fm_uc_incr                        true
% 2.49/0.99  --sat_out_model                         small
% 2.49/0.99  --sat_out_clauses                       false
% 2.49/0.99  
% 2.49/0.99  ------ QBF Options
% 2.49/0.99  
% 2.49/0.99  --qbf_mode                              false
% 2.49/0.99  --qbf_elim_univ                         false
% 2.49/0.99  --qbf_dom_inst                          none
% 2.49/0.99  --qbf_dom_pre_inst                      false
% 2.49/0.99  --qbf_sk_in                             false
% 2.49/0.99  --qbf_pred_elim                         true
% 2.49/0.99  --qbf_split                             512
% 2.49/0.99  
% 2.49/0.99  ------ BMC1 Options
% 2.49/0.99  
% 2.49/0.99  --bmc1_incremental                      false
% 2.49/0.99  --bmc1_axioms                           reachable_all
% 2.49/0.99  --bmc1_min_bound                        0
% 2.49/0.99  --bmc1_max_bound                        -1
% 2.49/0.99  --bmc1_max_bound_default                -1
% 2.49/0.99  --bmc1_symbol_reachability              true
% 2.49/0.99  --bmc1_property_lemmas                  false
% 2.49/0.99  --bmc1_k_induction                      false
% 2.49/0.99  --bmc1_non_equiv_states                 false
% 2.49/0.99  --bmc1_deadlock                         false
% 2.49/0.99  --bmc1_ucm                              false
% 2.49/0.99  --bmc1_add_unsat_core                   none
% 2.49/0.99  --bmc1_unsat_core_children              false
% 2.49/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/0.99  --bmc1_out_stat                         full
% 2.49/0.99  --bmc1_ground_init                      false
% 2.49/0.99  --bmc1_pre_inst_next_state              false
% 2.49/0.99  --bmc1_pre_inst_state                   false
% 2.49/0.99  --bmc1_pre_inst_reach_state             false
% 2.49/0.99  --bmc1_out_unsat_core                   false
% 2.49/0.99  --bmc1_aig_witness_out                  false
% 2.49/0.99  --bmc1_verbose                          false
% 2.49/0.99  --bmc1_dump_clauses_tptp                false
% 2.49/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.49/0.99  --bmc1_dump_file                        -
% 2.49/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.49/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.49/0.99  --bmc1_ucm_extend_mode                  1
% 2.49/0.99  --bmc1_ucm_init_mode                    2
% 2.49/0.99  --bmc1_ucm_cone_mode                    none
% 2.49/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.49/0.99  --bmc1_ucm_relax_model                  4
% 2.49/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.49/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/0.99  --bmc1_ucm_layered_model                none
% 2.49/0.99  --bmc1_ucm_max_lemma_size               10
% 2.49/0.99  
% 2.49/0.99  ------ AIG Options
% 2.49/0.99  
% 2.49/0.99  --aig_mode                              false
% 2.49/0.99  
% 2.49/0.99  ------ Instantiation Options
% 2.49/0.99  
% 2.49/0.99  --instantiation_flag                    true
% 2.49/0.99  --inst_sos_flag                         false
% 2.49/0.99  --inst_sos_phase                        true
% 2.49/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/0.99  --inst_lit_sel_side                     num_symb
% 2.49/0.99  --inst_solver_per_active                1400
% 2.49/0.99  --inst_solver_calls_frac                1.
% 2.49/0.99  --inst_passive_queue_type               priority_queues
% 2.49/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/0.99  --inst_passive_queues_freq              [25;2]
% 2.49/0.99  --inst_dismatching                      true
% 2.49/0.99  --inst_eager_unprocessed_to_passive     true
% 2.49/0.99  --inst_prop_sim_given                   true
% 2.49/0.99  --inst_prop_sim_new                     false
% 2.49/0.99  --inst_subs_new                         false
% 2.49/0.99  --inst_eq_res_simp                      false
% 2.49/0.99  --inst_subs_given                       false
% 2.49/0.99  --inst_orphan_elimination               true
% 2.49/0.99  --inst_learning_loop_flag               true
% 2.49/0.99  --inst_learning_start                   3000
% 2.49/0.99  --inst_learning_factor                  2
% 2.49/0.99  --inst_start_prop_sim_after_learn       3
% 2.49/0.99  --inst_sel_renew                        solver
% 2.49/0.99  --inst_lit_activity_flag                true
% 2.49/0.99  --inst_restr_to_given                   false
% 2.49/0.99  --inst_activity_threshold               500
% 2.49/0.99  --inst_out_proof                        true
% 2.49/0.99  
% 2.49/0.99  ------ Resolution Options
% 2.49/0.99  
% 2.49/0.99  --resolution_flag                       true
% 2.49/0.99  --res_lit_sel                           adaptive
% 2.49/0.99  --res_lit_sel_side                      none
% 2.49/0.99  --res_ordering                          kbo
% 2.49/0.99  --res_to_prop_solver                    active
% 2.49/0.99  --res_prop_simpl_new                    false
% 2.49/0.99  --res_prop_simpl_given                  true
% 2.49/0.99  --res_passive_queue_type                priority_queues
% 2.49/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/0.99  --res_passive_queues_freq               [15;5]
% 2.49/0.99  --res_forward_subs                      full
% 2.49/0.99  --res_backward_subs                     full
% 2.49/0.99  --res_forward_subs_resolution           true
% 2.49/0.99  --res_backward_subs_resolution          true
% 2.49/0.99  --res_orphan_elimination                true
% 2.49/0.99  --res_time_limit                        2.
% 2.49/0.99  --res_out_proof                         true
% 2.49/0.99  
% 2.49/0.99  ------ Superposition Options
% 2.49/0.99  
% 2.49/0.99  --superposition_flag                    true
% 2.49/0.99  --sup_passive_queue_type                priority_queues
% 2.49/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.49/0.99  --demod_completeness_check              fast
% 2.49/0.99  --demod_use_ground                      true
% 2.49/0.99  --sup_to_prop_solver                    passive
% 2.49/0.99  --sup_prop_simpl_new                    true
% 2.49/0.99  --sup_prop_simpl_given                  true
% 2.49/0.99  --sup_fun_splitting                     false
% 2.49/0.99  --sup_smt_interval                      50000
% 2.49/0.99  
% 2.49/0.99  ------ Superposition Simplification Setup
% 2.49/0.99  
% 2.49/0.99  --sup_indices_passive                   []
% 2.49/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_full_bw                           [BwDemod]
% 2.49/0.99  --sup_immed_triv                        [TrivRules]
% 2.49/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_immed_bw_main                     []
% 2.49/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.99  
% 2.49/0.99  ------ Combination Options
% 2.49/0.99  
% 2.49/0.99  --comb_res_mult                         3
% 2.49/0.99  --comb_sup_mult                         2
% 2.49/0.99  --comb_inst_mult                        10
% 2.49/0.99  
% 2.49/0.99  ------ Debug Options
% 2.49/0.99  
% 2.49/0.99  --dbg_backtrace                         false
% 2.49/0.99  --dbg_dump_prop_clauses                 false
% 2.49/0.99  --dbg_dump_prop_clauses_file            -
% 2.49/0.99  --dbg_out_stat                          false
% 2.49/0.99  ------ Parsing...
% 2.49/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/0.99  ------ Proving...
% 2.49/0.99  ------ Problem Properties 
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  clauses                                 17
% 2.49/0.99  conjectures                             2
% 2.49/0.99  EPR                                     2
% 2.49/0.99  Horn                                    17
% 2.49/0.99  unary                                   9
% 2.49/0.99  binary                                  4
% 2.49/0.99  lits                                    29
% 2.49/0.99  lits eq                                 13
% 2.49/0.99  fd_pure                                 0
% 2.49/0.99  fd_pseudo                               0
% 2.49/0.99  fd_cond                                 0
% 2.49/0.99  fd_pseudo_cond                          0
% 2.49/0.99  AC symbols                              0
% 2.49/0.99  
% 2.49/0.99  ------ Schedule dynamic 5 is on 
% 2.49/0.99  
% 2.49/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  ------ 
% 2.49/0.99  Current options:
% 2.49/0.99  ------ 
% 2.49/0.99  
% 2.49/0.99  ------ Input Options
% 2.49/0.99  
% 2.49/0.99  --out_options                           all
% 2.49/0.99  --tptp_safe_out                         true
% 2.49/0.99  --problem_path                          ""
% 2.49/0.99  --include_path                          ""
% 2.49/0.99  --clausifier                            res/vclausify_rel
% 2.49/0.99  --clausifier_options                    --mode clausify
% 2.49/0.99  --stdin                                 false
% 2.49/0.99  --stats_out                             all
% 2.49/0.99  
% 2.49/0.99  ------ General Options
% 2.49/0.99  
% 2.49/0.99  --fof                                   false
% 2.49/0.99  --time_out_real                         305.
% 2.49/0.99  --time_out_virtual                      -1.
% 2.49/0.99  --symbol_type_check                     false
% 2.49/0.99  --clausify_out                          false
% 2.49/0.99  --sig_cnt_out                           false
% 2.49/0.99  --trig_cnt_out                          false
% 2.49/0.99  --trig_cnt_out_tolerance                1.
% 2.49/0.99  --trig_cnt_out_sk_spl                   false
% 2.49/0.99  --abstr_cl_out                          false
% 2.49/0.99  
% 2.49/0.99  ------ Global Options
% 2.49/0.99  
% 2.49/0.99  --schedule                              default
% 2.49/0.99  --add_important_lit                     false
% 2.49/0.99  --prop_solver_per_cl                    1000
% 2.49/0.99  --min_unsat_core                        false
% 2.49/0.99  --soft_assumptions                      false
% 2.49/0.99  --soft_lemma_size                       3
% 2.49/0.99  --prop_impl_unit_size                   0
% 2.49/0.99  --prop_impl_unit                        []
% 2.49/0.99  --share_sel_clauses                     true
% 2.49/0.99  --reset_solvers                         false
% 2.49/0.99  --bc_imp_inh                            [conj_cone]
% 2.49/0.99  --conj_cone_tolerance                   3.
% 2.49/0.99  --extra_neg_conj                        none
% 2.49/0.99  --large_theory_mode                     true
% 2.49/0.99  --prolific_symb_bound                   200
% 2.49/0.99  --lt_threshold                          2000
% 2.49/0.99  --clause_weak_htbl                      true
% 2.49/0.99  --gc_record_bc_elim                     false
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing Options
% 2.49/0.99  
% 2.49/0.99  --preprocessing_flag                    true
% 2.49/0.99  --time_out_prep_mult                    0.1
% 2.49/0.99  --splitting_mode                        input
% 2.49/0.99  --splitting_grd                         true
% 2.49/0.99  --splitting_cvd                         false
% 2.49/0.99  --splitting_cvd_svl                     false
% 2.49/0.99  --splitting_nvd                         32
% 2.49/0.99  --sub_typing                            true
% 2.49/0.99  --prep_gs_sim                           true
% 2.49/0.99  --prep_unflatten                        true
% 2.49/0.99  --prep_res_sim                          true
% 2.49/0.99  --prep_upred                            true
% 2.49/0.99  --prep_sem_filter                       exhaustive
% 2.49/0.99  --prep_sem_filter_out                   false
% 2.49/0.99  --pred_elim                             true
% 2.49/0.99  --res_sim_input                         true
% 2.49/0.99  --eq_ax_congr_red                       true
% 2.49/0.99  --pure_diseq_elim                       true
% 2.49/0.99  --brand_transform                       false
% 2.49/0.99  --non_eq_to_eq                          false
% 2.49/0.99  --prep_def_merge                        true
% 2.49/0.99  --prep_def_merge_prop_impl              false
% 2.49/0.99  --prep_def_merge_mbd                    true
% 2.49/0.99  --prep_def_merge_tr_red                 false
% 2.49/0.99  --prep_def_merge_tr_cl                  false
% 2.49/0.99  --smt_preprocessing                     true
% 2.49/0.99  --smt_ac_axioms                         fast
% 2.49/0.99  --preprocessed_out                      false
% 2.49/0.99  --preprocessed_stats                    false
% 2.49/0.99  
% 2.49/0.99  ------ Abstraction refinement Options
% 2.49/0.99  
% 2.49/0.99  --abstr_ref                             []
% 2.49/0.99  --abstr_ref_prep                        false
% 2.49/0.99  --abstr_ref_until_sat                   false
% 2.49/0.99  --abstr_ref_sig_restrict                funpre
% 2.49/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/0.99  --abstr_ref_under                       []
% 2.49/0.99  
% 2.49/0.99  ------ SAT Options
% 2.49/0.99  
% 2.49/0.99  --sat_mode                              false
% 2.49/0.99  --sat_fm_restart_options                ""
% 2.49/0.99  --sat_gr_def                            false
% 2.49/0.99  --sat_epr_types                         true
% 2.49/0.99  --sat_non_cyclic_types                  false
% 2.49/0.99  --sat_finite_models                     false
% 2.49/0.99  --sat_fm_lemmas                         false
% 2.49/0.99  --sat_fm_prep                           false
% 2.49/0.99  --sat_fm_uc_incr                        true
% 2.49/0.99  --sat_out_model                         small
% 2.49/0.99  --sat_out_clauses                       false
% 2.49/0.99  
% 2.49/0.99  ------ QBF Options
% 2.49/0.99  
% 2.49/0.99  --qbf_mode                              false
% 2.49/0.99  --qbf_elim_univ                         false
% 2.49/0.99  --qbf_dom_inst                          none
% 2.49/0.99  --qbf_dom_pre_inst                      false
% 2.49/0.99  --qbf_sk_in                             false
% 2.49/0.99  --qbf_pred_elim                         true
% 2.49/0.99  --qbf_split                             512
% 2.49/0.99  
% 2.49/0.99  ------ BMC1 Options
% 2.49/0.99  
% 2.49/0.99  --bmc1_incremental                      false
% 2.49/0.99  --bmc1_axioms                           reachable_all
% 2.49/0.99  --bmc1_min_bound                        0
% 2.49/0.99  --bmc1_max_bound                        -1
% 2.49/0.99  --bmc1_max_bound_default                -1
% 2.49/0.99  --bmc1_symbol_reachability              true
% 2.49/0.99  --bmc1_property_lemmas                  false
% 2.49/0.99  --bmc1_k_induction                      false
% 2.49/0.99  --bmc1_non_equiv_states                 false
% 2.49/0.99  --bmc1_deadlock                         false
% 2.49/0.99  --bmc1_ucm                              false
% 2.49/0.99  --bmc1_add_unsat_core                   none
% 2.49/0.99  --bmc1_unsat_core_children              false
% 2.49/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/0.99  --bmc1_out_stat                         full
% 2.49/0.99  --bmc1_ground_init                      false
% 2.49/0.99  --bmc1_pre_inst_next_state              false
% 2.49/0.99  --bmc1_pre_inst_state                   false
% 2.49/0.99  --bmc1_pre_inst_reach_state             false
% 2.49/0.99  --bmc1_out_unsat_core                   false
% 2.49/0.99  --bmc1_aig_witness_out                  false
% 2.49/0.99  --bmc1_verbose                          false
% 2.49/0.99  --bmc1_dump_clauses_tptp                false
% 2.49/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.49/0.99  --bmc1_dump_file                        -
% 2.49/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.49/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.49/0.99  --bmc1_ucm_extend_mode                  1
% 2.49/0.99  --bmc1_ucm_init_mode                    2
% 2.49/0.99  --bmc1_ucm_cone_mode                    none
% 2.49/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.49/0.99  --bmc1_ucm_relax_model                  4
% 2.49/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.49/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/0.99  --bmc1_ucm_layered_model                none
% 2.49/0.99  --bmc1_ucm_max_lemma_size               10
% 2.49/0.99  
% 2.49/0.99  ------ AIG Options
% 2.49/0.99  
% 2.49/0.99  --aig_mode                              false
% 2.49/0.99  
% 2.49/0.99  ------ Instantiation Options
% 2.49/0.99  
% 2.49/0.99  --instantiation_flag                    true
% 2.49/0.99  --inst_sos_flag                         false
% 2.49/0.99  --inst_sos_phase                        true
% 2.49/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/0.99  --inst_lit_sel_side                     none
% 2.49/0.99  --inst_solver_per_active                1400
% 2.49/0.99  --inst_solver_calls_frac                1.
% 2.49/0.99  --inst_passive_queue_type               priority_queues
% 2.49/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/0.99  --inst_passive_queues_freq              [25;2]
% 2.49/0.99  --inst_dismatching                      true
% 2.49/0.99  --inst_eager_unprocessed_to_passive     true
% 2.49/0.99  --inst_prop_sim_given                   true
% 2.49/0.99  --inst_prop_sim_new                     false
% 2.49/0.99  --inst_subs_new                         false
% 2.49/0.99  --inst_eq_res_simp                      false
% 2.49/0.99  --inst_subs_given                       false
% 2.49/0.99  --inst_orphan_elimination               true
% 2.49/0.99  --inst_learning_loop_flag               true
% 2.49/0.99  --inst_learning_start                   3000
% 2.49/0.99  --inst_learning_factor                  2
% 2.49/0.99  --inst_start_prop_sim_after_learn       3
% 2.49/0.99  --inst_sel_renew                        solver
% 2.49/0.99  --inst_lit_activity_flag                true
% 2.49/0.99  --inst_restr_to_given                   false
% 2.49/0.99  --inst_activity_threshold               500
% 2.49/0.99  --inst_out_proof                        true
% 2.49/0.99  
% 2.49/0.99  ------ Resolution Options
% 2.49/0.99  
% 2.49/0.99  --resolution_flag                       false
% 2.49/0.99  --res_lit_sel                           adaptive
% 2.49/0.99  --res_lit_sel_side                      none
% 2.49/0.99  --res_ordering                          kbo
% 2.49/0.99  --res_to_prop_solver                    active
% 2.49/0.99  --res_prop_simpl_new                    false
% 2.49/0.99  --res_prop_simpl_given                  true
% 2.49/0.99  --res_passive_queue_type                priority_queues
% 2.49/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/0.99  --res_passive_queues_freq               [15;5]
% 2.49/0.99  --res_forward_subs                      full
% 2.49/0.99  --res_backward_subs                     full
% 2.49/0.99  --res_forward_subs_resolution           true
% 2.49/0.99  --res_backward_subs_resolution          true
% 2.49/0.99  --res_orphan_elimination                true
% 2.49/0.99  --res_time_limit                        2.
% 2.49/0.99  --res_out_proof                         true
% 2.49/0.99  
% 2.49/0.99  ------ Superposition Options
% 2.49/0.99  
% 2.49/0.99  --superposition_flag                    true
% 2.49/0.99  --sup_passive_queue_type                priority_queues
% 2.49/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.49/0.99  --demod_completeness_check              fast
% 2.49/0.99  --demod_use_ground                      true
% 2.49/0.99  --sup_to_prop_solver                    passive
% 2.49/0.99  --sup_prop_simpl_new                    true
% 2.49/0.99  --sup_prop_simpl_given                  true
% 2.49/0.99  --sup_fun_splitting                     false
% 2.49/0.99  --sup_smt_interval                      50000
% 2.49/0.99  
% 2.49/0.99  ------ Superposition Simplification Setup
% 2.49/0.99  
% 2.49/0.99  --sup_indices_passive                   []
% 2.49/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_full_bw                           [BwDemod]
% 2.49/0.99  --sup_immed_triv                        [TrivRules]
% 2.49/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_immed_bw_main                     []
% 2.49/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.99  
% 2.49/0.99  ------ Combination Options
% 2.49/0.99  
% 2.49/0.99  --comb_res_mult                         3
% 2.49/0.99  --comb_sup_mult                         2
% 2.49/0.99  --comb_inst_mult                        10
% 2.49/0.99  
% 2.49/0.99  ------ Debug Options
% 2.49/0.99  
% 2.49/0.99  --dbg_backtrace                         false
% 2.49/0.99  --dbg_dump_prop_clauses                 false
% 2.49/0.99  --dbg_dump_prop_clauses_file            -
% 2.49/0.99  --dbg_out_stat                          false
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  ------ Proving...
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  % SZS status Theorem for theBenchmark.p
% 2.49/0.99  
% 2.49/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.49/0.99  
% 2.49/0.99  fof(f9,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f21,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f9])).
% 2.49/0.99  
% 2.49/0.99  fof(f22,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f21])).
% 2.49/0.99  
% 2.49/0.99  fof(f46,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f22])).
% 2.49/0.99  
% 2.49/0.99  fof(f14,conjecture,(
% 2.49/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f15,negated_conjecture,(
% 2.49/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 2.49/0.99    inference(negated_conjecture,[],[f14])).
% 2.49/0.99  
% 2.49/0.99  fof(f29,plain,(
% 2.49/0.99    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f15])).
% 2.49/0.99  
% 2.49/0.99  fof(f30,plain,(
% 2.49/0.99    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f29])).
% 2.49/0.99  
% 2.49/0.99  fof(f35,plain,(
% 2.49/0.99    ( ! [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,X0) & v3_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.49/0.99    introduced(choice_axiom,[])).
% 2.49/0.99  
% 2.49/0.99  fof(f34,plain,(
% 2.49/0.99    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.49/0.99    introduced(choice_axiom,[])).
% 2.49/0.99  
% 2.49/0.99  fof(f36,plain,(
% 2.49/0.99    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f35,f34])).
% 2.49/0.99  
% 2.49/0.99  fof(f56,plain,(
% 2.49/0.99    v3_pre_topc(sK1,sK0)),
% 2.49/0.99    inference(cnf_transformation,[],[f36])).
% 2.49/0.99  
% 2.49/0.99  fof(f54,plain,(
% 2.49/0.99    l1_pre_topc(sK0)),
% 2.49/0.99    inference(cnf_transformation,[],[f36])).
% 2.49/0.99  
% 2.49/0.99  fof(f55,plain,(
% 2.49/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.49/0.99    inference(cnf_transformation,[],[f36])).
% 2.49/0.99  
% 2.49/0.99  fof(f6,axiom,(
% 2.49/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f17,plain,(
% 2.49/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f6])).
% 2.49/0.99  
% 2.49/0.99  fof(f18,plain,(
% 2.49/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f17])).
% 2.49/0.99  
% 2.49/0.99  fof(f42,plain,(
% 2.49/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f18])).
% 2.49/0.99  
% 2.49/0.99  fof(f5,axiom,(
% 2.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f16,plain,(
% 2.49/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f5])).
% 2.49/0.99  
% 2.49/0.99  fof(f41,plain,(
% 2.49/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.49/0.99    inference(cnf_transformation,[],[f16])).
% 2.49/0.99  
% 2.49/0.99  fof(f12,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f26,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f12])).
% 2.49/0.99  
% 2.49/0.99  fof(f33,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(nnf_transformation,[],[f26])).
% 2.49/0.99  
% 2.49/0.99  fof(f50,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f33])).
% 2.49/0.99  
% 2.49/0.99  fof(f13,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f27,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f13])).
% 2.49/0.99  
% 2.49/0.99  fof(f28,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f27])).
% 2.49/0.99  
% 2.49/0.99  fof(f52,plain,(
% 2.49/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f28])).
% 2.49/0.99  
% 2.49/0.99  fof(f57,plain,(
% 2.49/0.99    v3_tops_1(sK1,sK0)),
% 2.49/0.99    inference(cnf_transformation,[],[f36])).
% 2.49/0.99  
% 2.49/0.99  fof(f8,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f20,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f8])).
% 2.49/0.99  
% 2.49/0.99  fof(f45,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f20])).
% 2.49/0.99  
% 2.49/0.99  fof(f3,axiom,(
% 2.49/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f39,plain,(
% 2.49/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.49/0.99    inference(cnf_transformation,[],[f3])).
% 2.49/0.99  
% 2.49/0.99  fof(f7,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f19,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f7])).
% 2.49/0.99  
% 2.49/0.99  fof(f31,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(nnf_transformation,[],[f19])).
% 2.49/0.99  
% 2.49/0.99  fof(f43,plain,(
% 2.49/0.99    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f31])).
% 2.49/0.99  
% 2.49/0.99  fof(f10,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f23,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f10])).
% 2.49/0.99  
% 2.49/0.99  fof(f47,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f23])).
% 2.49/0.99  
% 2.49/0.99  fof(f11,axiom,(
% 2.49/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f24,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f11])).
% 2.49/0.99  
% 2.49/0.99  fof(f25,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f24])).
% 2.49/0.99  
% 2.49/0.99  fof(f32,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/0.99    inference(nnf_transformation,[],[f25])).
% 2.49/0.99  
% 2.49/0.99  fof(f48,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f32])).
% 2.49/0.99  
% 2.49/0.99  fof(f53,plain,(
% 2.49/0.99    v2_pre_topc(sK0)),
% 2.49/0.99    inference(cnf_transformation,[],[f36])).
% 2.49/0.99  
% 2.49/0.99  fof(f1,axiom,(
% 2.49/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f37,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f1])).
% 2.49/0.99  
% 2.49/0.99  fof(f4,axiom,(
% 2.49/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f40,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.49/0.99    inference(cnf_transformation,[],[f4])).
% 2.49/0.99  
% 2.49/0.99  fof(f59,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.49/0.99    inference(definition_unfolding,[],[f37,f40,f40])).
% 2.49/0.99  
% 2.49/0.99  fof(f2,axiom,(
% 2.49/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f38,plain,(
% 2.49/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.49/0.99    inference(cnf_transformation,[],[f2])).
% 2.49/0.99  
% 2.49/0.99  fof(f60,plain,(
% 2.49/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.49/0.99    inference(definition_unfolding,[],[f38,f40])).
% 2.49/0.99  
% 2.49/0.99  fof(f58,plain,(
% 2.49/0.99    k1_xboole_0 != sK1),
% 2.49/0.99    inference(cnf_transformation,[],[f36])).
% 2.49/0.99  
% 2.49/0.99  cnf(c_8,plain,
% 2.49/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_17,negated_conjecture,
% 2.49/0.99      ( v3_pre_topc(sK1,sK0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_251,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0)
% 2.49/0.99      | sK0 != X1
% 2.49/0.99      | sK1 != X0 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_252,plain,
% 2.49/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | ~ l1_pre_topc(sK0)
% 2.49/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_251]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_19,negated_conjecture,
% 2.49/0.99      ( l1_pre_topc(sK0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_18,negated_conjecture,
% 2.49/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.49/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_254,plain,
% 2.49/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_252,c_19,c_18]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_413,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | sK0 != X1 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_414,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_413]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_739,plain,
% 2.49/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.49/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_938,plain,
% 2.49/0.99      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.49/0.99      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_254,c_739]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_23,plain,
% 2.49/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_833,plain,
% 2.49/0.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_414]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_834,plain,
% 2.49/0.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.49/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1440,plain,
% 2.49/0.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_938,c_23,c_834]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.49/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.49/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_749,plain,
% 2.49/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.49/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1647,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_1440,c_749]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_748,plain,
% 2.49/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_13,plain,
% 2.49/0.99      ( ~ v2_tops_1(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.49/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_359,plain,
% 2.49/0.99      ( ~ v2_tops_1(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.49/0.99      | sK0 != X1 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_360,plain,
% 2.49/0.99      ( ~ v2_tops_1(X0,sK0)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_359]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_743,plain,
% 2.49/0.99      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.49/0.99      | v2_tops_1(X0,sK0) != iProver_top
% 2.49/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1370,plain,
% 2.49/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.49/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_748,c_743]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_14,plain,
% 2.49/0.99      ( v2_tops_1(X0,X1)
% 2.49/0.99      | ~ v3_tops_1(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_16,negated_conjecture,
% 2.49/0.99      ( v3_tops_1(sK1,sK0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_324,plain,
% 2.49/0.99      ( v2_tops_1(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | sK0 != X1
% 2.49/0.99      | sK1 != X0 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_325,plain,
% 2.49/0.99      ( v2_tops_1(sK1,sK0)
% 2.49/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | ~ l1_pre_topc(sK0) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_840,plain,
% 2.49/0.99      ( ~ v2_tops_1(sK1,sK0)
% 2.49/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_360]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1387,plain,
% 2.49/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_1370,c_19,c_18,c_325,c_840]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_7,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_401,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.49/0.99      | sK0 != X1 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_402,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_740,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.49/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1020,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_748,c_740]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1390,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_1387,c_1020]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1903,plain,
% 2.49/0.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_1647,c_1390]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2,plain,
% 2.49/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.49/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1905,plain,
% 2.49/0.99      ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_1903,c_2]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1445,plain,
% 2.49/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
% 2.49/0.99      | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_1440,c_743]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_6,plain,
% 2.49/0.99      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 2.49/0.99      | ~ v3_tops_1(X1,X0)
% 2.49/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/0.99      | ~ l1_pre_topc(X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_313,plain,
% 2.49/0.99      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 2.49/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/0.99      | ~ l1_pre_topc(X0)
% 2.49/0.99      | sK0 != X0
% 2.49/0.99      | sK1 != X1 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_314,plain,
% 2.49/0.99      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 2.49/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | ~ l1_pre_topc(sK0) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_313]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_837,plain,
% 2.49/0.99      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 2.49/0.99      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_360]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1958,plain,
% 2.49/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_1445,c_19,c_18,c_314,c_833,c_837]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1961,plain,
% 2.49/0.99      ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_1958,c_254]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2126,plain,
% 2.49/0.99      ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) ),
% 2.49/0.99      inference(light_normalisation,[status(thm)],[c_1905,c_1961]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_9,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_389,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 2.49/0.99      | sK0 != X1 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_390,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_389]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_741,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 2.49/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_943,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_748,c_741]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1391,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_1387,c_943]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1645,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_748,c_749]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1662,plain,
% 2.49/0.99      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_1391,c_1645]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2129,plain,
% 2.49/0.99      ( k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_2126,c_1662]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_11,plain,
% 2.49/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ v2_pre_topc(X1)
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X0) = k2_tops_1(X1,X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_20,negated_conjecture,
% 2.49/0.99      ( v2_pre_topc(sK0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_200,plain,
% 2.49/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X0) = k2_tops_1(X1,X0)
% 2.49/0.99      | sK0 != X1 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_201,plain,
% 2.49/0.99      ( ~ v3_pre_topc(X0,sK0)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | ~ l1_pre_topc(sK0)
% 2.49/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X0) = k2_tops_1(sK0,X0) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_200]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_205,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | ~ v3_pre_topc(X0,sK0)
% 2.49/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X0) = k2_tops_1(sK0,X0) ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_201,c_19]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_206,plain,
% 2.49/0.99      ( ~ v3_pre_topc(X0,sK0)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X0) = k2_tops_1(sK0,X0) ),
% 2.49/0.99      inference(renaming,[status(thm)],[c_205]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_280,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X0) = k2_tops_1(sK0,X0)
% 2.49/0.99      | sK0 != sK0
% 2.49/0.99      | sK1 != X0 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_206]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_281,plain,
% 2.49/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.49/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_283,plain,
% 2.49/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_281,c_18]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1726,plain,
% 2.49/0.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_1647,c_283]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_0,plain,
% 2.49/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.49/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1805,plain,
% 2.49/0.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_1726,c_0]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1965,plain,
% 2.49/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0))) = k4_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_tops_1(sK0,sK1)) ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_1961,c_1805]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2176,plain,
% 2.49/0.99      ( k4_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0))) ),
% 2.49/0.99      inference(light_normalisation,[status(thm)],[c_1965,c_2126]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1,plain,
% 2.49/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.49/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_760,plain,
% 2.49/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.49/0.99      inference(light_normalisation,[status(thm)],[c_1,c_2]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2177,plain,
% 2.49/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_2176,c_760]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2180,plain,
% 2.49/0.99      ( k4_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_2129,c_2177]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_530,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_854,plain,
% 2.49/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_530]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1907,plain,
% 2.49/0.99      ( sK1 != k4_xboole_0(sK1,k1_xboole_0)
% 2.49/0.99      | k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
% 2.49/0.99      | k1_xboole_0 = sK1 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_854]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1767,plain,
% 2.49/0.99      ( X0 != X1
% 2.49/0.99      | X0 = k4_xboole_0(sK1,k1_xboole_0)
% 2.49/0.99      | k4_xboole_0(sK1,k1_xboole_0) != X1 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_530]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1768,plain,
% 2.49/0.99      ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
% 2.49/0.99      | k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
% 2.49/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_1767]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_902,plain,
% 2.49/0.99      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_530]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1083,plain,
% 2.49/0.99      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_902]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1338,plain,
% 2.49/0.99      ( k4_xboole_0(sK1,k1_xboole_0) != sK1
% 2.49/0.99      | sK1 = k4_xboole_0(sK1,k1_xboole_0)
% 2.49/0.99      | sK1 != sK1 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_1083]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_529,plain,( X0 = X0 ),theory(equality) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_910,plain,
% 2.49/0.99      ( sK1 = sK1 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_529]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_904,plain,
% 2.49/0.99      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_550,plain,
% 2.49/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_529]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_15,negated_conjecture,
% 2.49/0.99      ( k1_xboole_0 != sK1 ),
% 2.49/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(contradiction,plain,
% 2.49/0.99      ( $false ),
% 2.49/0.99      inference(minisat,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_2180,c_1907,c_1768,c_1338,c_910,c_904,c_550,c_15]) ).
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/0.99  
% 2.49/0.99  ------                               Statistics
% 2.49/0.99  
% 2.49/0.99  ------ General
% 2.49/0.99  
% 2.49/0.99  abstr_ref_over_cycles:                  0
% 2.49/0.99  abstr_ref_under_cycles:                 0
% 2.49/0.99  gc_basic_clause_elim:                   0
% 2.49/0.99  forced_gc_time:                         0
% 2.49/0.99  parsing_time:                           0.01
% 2.49/0.99  unif_index_cands_time:                  0.
% 2.49/0.99  unif_index_add_time:                    0.
% 2.49/0.99  orderings_time:                         0.
% 2.49/0.99  out_proof_time:                         0.008
% 2.49/0.99  total_time:                             0.083
% 2.49/0.99  num_of_symbols:                         47
% 2.49/0.99  num_of_terms:                           1817
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing
% 2.49/0.99  
% 2.49/0.99  num_of_splits:                          0
% 2.49/0.99  num_of_split_atoms:                     0
% 2.49/0.99  num_of_reused_defs:                     0
% 2.49/0.99  num_eq_ax_congr_red:                    8
% 2.49/0.99  num_of_sem_filtered_clauses:            1
% 2.49/0.99  num_of_subtypes:                        0
% 2.49/0.99  monotx_restored_types:                  0
% 2.49/0.99  sat_num_of_epr_types:                   0
% 2.49/0.99  sat_num_of_non_cyclic_types:            0
% 2.49/0.99  sat_guarded_non_collapsed_types:        0
% 2.49/0.99  num_pure_diseq_elim:                    0
% 2.49/0.99  simp_replaced_by:                       0
% 2.49/0.99  res_preprocessed:                       95
% 2.49/0.99  prep_upred:                             0
% 2.49/0.99  prep_unflattend:                        19
% 2.49/0.99  smt_new_axioms:                         0
% 2.49/0.99  pred_elim_cands:                        2
% 2.49/0.99  pred_elim:                              4
% 2.49/0.99  pred_elim_cl:                           4
% 2.49/0.99  pred_elim_cycles:                       6
% 2.49/0.99  merged_defs:                            0
% 2.49/0.99  merged_defs_ncl:                        0
% 2.49/0.99  bin_hyper_res:                          0
% 2.49/0.99  prep_cycles:                            4
% 2.49/0.99  pred_elim_time:                         0.003
% 2.49/0.99  splitting_time:                         0.
% 2.49/0.99  sem_filter_time:                        0.
% 2.49/0.99  monotx_time:                            0.
% 2.49/0.99  subtype_inf_time:                       0.
% 2.49/0.99  
% 2.49/0.99  ------ Problem properties
% 2.49/0.99  
% 2.49/0.99  clauses:                                17
% 2.49/0.99  conjectures:                            2
% 2.49/0.99  epr:                                    2
% 2.49/0.99  horn:                                   17
% 2.49/0.99  ground:                                 6
% 2.49/0.99  unary:                                  9
% 2.49/0.99  binary:                                 4
% 2.49/0.99  lits:                                   29
% 2.49/0.99  lits_eq:                                13
% 2.49/0.99  fd_pure:                                0
% 2.49/0.99  fd_pseudo:                              0
% 2.49/0.99  fd_cond:                                0
% 2.49/0.99  fd_pseudo_cond:                         0
% 2.49/0.99  ac_symbols:                             0
% 2.49/0.99  
% 2.49/0.99  ------ Propositional Solver
% 2.49/0.99  
% 2.49/0.99  prop_solver_calls:                      27
% 2.49/0.99  prop_fast_solver_calls:                 524
% 2.49/0.99  smt_solver_calls:                       0
% 2.49/0.99  smt_fast_solver_calls:                  0
% 2.49/0.99  prop_num_of_clauses:                    852
% 2.49/0.99  prop_preprocess_simplified:             3078
% 2.49/0.99  prop_fo_subsumed:                       13
% 2.49/0.99  prop_solver_time:                       0.
% 2.49/0.99  smt_solver_time:                        0.
% 2.49/0.99  smt_fast_solver_time:                   0.
% 2.49/0.99  prop_fast_solver_time:                  0.
% 2.49/0.99  prop_unsat_core_time:                   0.
% 2.49/0.99  
% 2.49/0.99  ------ QBF
% 2.49/0.99  
% 2.49/0.99  qbf_q_res:                              0
% 2.49/0.99  qbf_num_tautologies:                    0
% 2.49/0.99  qbf_prep_cycles:                        0
% 2.49/0.99  
% 2.49/0.99  ------ BMC1
% 2.49/0.99  
% 2.49/0.99  bmc1_current_bound:                     -1
% 2.49/0.99  bmc1_last_solved_bound:                 -1
% 2.49/0.99  bmc1_unsat_core_size:                   -1
% 2.49/0.99  bmc1_unsat_core_parents_size:           -1
% 2.49/0.99  bmc1_merge_next_fun:                    0
% 2.49/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.49/0.99  
% 2.49/0.99  ------ Instantiation
% 2.49/0.99  
% 2.49/0.99  inst_num_of_clauses:                    299
% 2.49/0.99  inst_num_in_passive:                    89
% 2.49/0.99  inst_num_in_active:                     180
% 2.49/0.99  inst_num_in_unprocessed:                30
% 2.49/0.99  inst_num_of_loops:                      190
% 2.49/0.99  inst_num_of_learning_restarts:          0
% 2.49/0.99  inst_num_moves_active_passive:          6
% 2.49/0.99  inst_lit_activity:                      0
% 2.49/0.99  inst_lit_activity_moves:                0
% 2.49/0.99  inst_num_tautologies:                   0
% 2.49/0.99  inst_num_prop_implied:                  0
% 2.49/0.99  inst_num_existing_simplified:           0
% 2.49/0.99  inst_num_eq_res_simplified:             0
% 2.49/0.99  inst_num_child_elim:                    0
% 2.49/0.99  inst_num_of_dismatching_blockings:      9
% 2.49/0.99  inst_num_of_non_proper_insts:           196
% 2.49/0.99  inst_num_of_duplicates:                 0
% 2.49/0.99  inst_inst_num_from_inst_to_res:         0
% 2.49/0.99  inst_dismatching_checking_time:         0.
% 2.49/0.99  
% 2.49/0.99  ------ Resolution
% 2.49/0.99  
% 2.49/0.99  res_num_of_clauses:                     0
% 2.49/0.99  res_num_in_passive:                     0
% 2.49/0.99  res_num_in_active:                      0
% 2.49/0.99  res_num_of_loops:                       99
% 2.49/0.99  res_forward_subset_subsumed:            19
% 2.49/0.99  res_backward_subset_subsumed:           0
% 2.49/0.99  res_forward_subsumed:                   0
% 2.49/0.99  res_backward_subsumed:                  0
% 2.49/0.99  res_forward_subsumption_resolution:     0
% 2.49/0.99  res_backward_subsumption_resolution:    0
% 2.49/0.99  res_clause_to_clause_subsumption:       83
% 2.49/0.99  res_orphan_elimination:                 0
% 2.49/0.99  res_tautology_del:                      17
% 2.49/0.99  res_num_eq_res_simplified:              0
% 2.49/0.99  res_num_sel_changes:                    0
% 2.49/0.99  res_moves_from_active_to_pass:          0
% 2.49/0.99  
% 2.49/0.99  ------ Superposition
% 2.49/0.99  
% 2.49/0.99  sup_time_total:                         0.
% 2.49/0.99  sup_time_generating:                    0.
% 2.49/0.99  sup_time_sim_full:                      0.
% 2.49/0.99  sup_time_sim_immed:                     0.
% 2.49/0.99  
% 2.49/0.99  sup_num_of_clauses:                     40
% 2.49/0.99  sup_num_in_active:                      22
% 2.49/0.99  sup_num_in_passive:                     18
% 2.49/0.99  sup_num_of_loops:                       37
% 2.49/0.99  sup_fw_superposition:                   32
% 2.49/0.99  sup_bw_superposition:                   17
% 2.49/0.99  sup_immediate_simplified:               14
% 2.49/0.99  sup_given_eliminated:                   0
% 2.49/0.99  comparisons_done:                       0
% 2.49/0.99  comparisons_avoided:                    0
% 2.49/0.99  
% 2.49/0.99  ------ Simplifications
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  sim_fw_subset_subsumed:                 8
% 2.49/0.99  sim_bw_subset_subsumed:                 0
% 2.49/0.99  sim_fw_subsumed:                        2
% 2.49/0.99  sim_bw_subsumed:                        0
% 2.49/0.99  sim_fw_subsumption_res:                 0
% 2.49/0.99  sim_bw_subsumption_res:                 0
% 2.49/0.99  sim_tautology_del:                      0
% 2.49/0.99  sim_eq_tautology_del:                   2
% 2.49/0.99  sim_eq_res_simp:                        0
% 2.49/0.99  sim_fw_demodulated:                     2
% 2.49/0.99  sim_bw_demodulated:                     15
% 2.49/0.99  sim_light_normalised:                   8
% 2.49/0.99  sim_joinable_taut:                      0
% 2.49/0.99  sim_joinable_simp:                      0
% 2.49/0.99  sim_ac_normalised:                      0
% 2.49/0.99  sim_smt_subsumption:                    0
% 2.49/0.99  
%------------------------------------------------------------------------------
