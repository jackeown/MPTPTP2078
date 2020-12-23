%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:25 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :  162 (1697 expanded)
%              Number of clauses        :   96 ( 505 expanded)
%              Number of leaves         :   19 ( 362 expanded)
%              Depth                    :   25
%              Number of atoms          :  436 (7292 expanded)
%              Number of equality atoms :  192 (2165 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK2),sK2) != k2_tops_1(X0,sK2)
          | ~ v3_pre_topc(sK2,X0) )
        & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK2),sK2) = k2_tops_1(X0,sK2)
          | v3_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) != k2_tops_1(sK1,X1)
            | ~ v3_pre_topc(X1,sK1) )
          & ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) = k2_tops_1(sK1,X1)
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2)
      | ~ v3_pre_topc(sK2,sK1) )
    & ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_226,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_12])).

cnf(c_777,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_269,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_789,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_12])).

cnf(c_779,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_2506,plain,
    ( v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_779])).

cnf(c_2527,plain,
    ( v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_2506])).

cnf(c_4181,plain,
    ( sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_777,c_19,c_20,c_269,c_2527])).

cnf(c_15,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_774,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_773,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_225,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_12])).

cnf(c_778,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_1336,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | v3_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_778])).

cnf(c_2085,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | k1_tops_1(sK1,sK2) = sK2
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1336,c_20])).

cnf(c_2086,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | v3_pre_topc(sK2,sK1) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_2085])).

cnf(c_2092,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | k1_tops_1(sK1,sK2) = sK2
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_2086])).

cnf(c_4186,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | k1_tops_1(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_4181,c_2092])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_788,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2797,plain,
    ( k5_xboole_0(k2_pre_topc(X0,X1),k1_setfam_1(k2_tarski(k2_pre_topc(X0,X1),X2))) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_788])).

cnf(c_16439,plain,
    ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_2797])).

cnf(c_1023,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1216,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_16581,plain,
    ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16439,c_17,c_16,c_1023,c_1216])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_784,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2742,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_784])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1028,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1029,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1028])).

cnf(c_3368,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2742,c_20,c_21,c_1029])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_786,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_790,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1373,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_790])).

cnf(c_4320,plain,
    ( k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3368,c_1373])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_792,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4548,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK1,sK2),sK2),k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4320,c_792])).

cnf(c_1285,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK1,sK2))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1286,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1285])).

cnf(c_5537,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4548,c_20,c_21,c_1029,c_1286])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_793,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5543,plain,
    ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),sK2))) = k3_subset_1(k2_pre_topc(sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_5537,c_793])).

cnf(c_16589,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k3_subset_1(k2_pre_topc(sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_16581,c_5543])).

cnf(c_16810,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | k3_subset_1(k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_4186,c_16589])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_787,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5542,plain,
    ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0)) = k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5537,c_787])).

cnf(c_5545,plain,
    ( k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_5537,c_788])).

cnf(c_1904,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(superposition,[status(thm)],[c_773,c_788])).

cnf(c_5547,plain,
    ( k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_5545,c_1904])).

cnf(c_5551,plain,
    ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0)) = k7_subset_1(u1_struct_0(sK1),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5542,c_5547])).

cnf(c_6611,plain,
    ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_5551])).

cnf(c_10609,plain,
    ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),sK2))) = k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_5537,c_6611])).

cnf(c_10611,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = k9_subset_1(k2_pre_topc(sK1,sK2),sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_10609,c_4320])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_791,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_995,plain,
    ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(X0))
    | k9_subset_1(X0,X1,X1) = X1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1190,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_791,c_4,c_995])).

cnf(c_10612,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_10611,c_1190])).

cnf(c_16913,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = sK2
    | k1_tops_1(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_16810,c_10612])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_776,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3159,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_776])).

cnf(c_1119,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3522,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3159,c_17,c_16,c_1119])).

cnf(c_16937,plain,
    ( k1_tops_1(sK1,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_16913,c_3522])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_783,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4008,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_783])).

cnf(c_1129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4322,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4008,c_17,c_16,c_1129])).

cnf(c_16962,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_16937,c_4322])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_228,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_11])).

cnf(c_229,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_11])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_11])).

cnf(c_483,plain,
    ( k1_tops_1(X1,X0) != X0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_229,c_227])).

cnf(c_484,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_1124,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_14,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16962,c_16937,c_1124,c_14,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 6.67/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.67/1.52  
% 6.67/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.67/1.52  
% 6.67/1.52  ------  iProver source info
% 6.67/1.52  
% 6.67/1.52  git: date: 2020-06-30 10:37:57 +0100
% 6.67/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.67/1.52  git: non_committed_changes: false
% 6.67/1.52  git: last_make_outside_of_git: false
% 6.67/1.52  
% 6.67/1.52  ------ 
% 6.67/1.52  ------ Parsing...
% 6.67/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.67/1.52  
% 6.67/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 6.67/1.52  
% 6.67/1.52  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.67/1.52  
% 6.67/1.52  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.67/1.52  ------ Proving...
% 6.67/1.52  ------ Problem Properties 
% 6.67/1.52  
% 6.67/1.52  
% 6.67/1.52  clauses                                 23
% 6.67/1.52  conjectures                             5
% 6.67/1.52  EPR                                     4
% 6.67/1.52  Horn                                    20
% 6.67/1.52  unary                                   4
% 6.67/1.52  binary                                  10
% 6.67/1.52  lits                                    57
% 6.67/1.52  lits eq                                 11
% 6.67/1.52  fd_pure                                 0
% 6.67/1.52  fd_pseudo                               0
% 6.67/1.52  fd_cond                                 0
% 6.67/1.52  fd_pseudo_cond                          0
% 6.67/1.52  AC symbols                              0
% 6.67/1.52  
% 6.67/1.52  ------ Input Options Time Limit: Unbounded
% 6.67/1.52  
% 6.67/1.52  
% 6.67/1.52  ------ 
% 6.67/1.52  Current options:
% 6.67/1.52  ------ 
% 6.67/1.52  
% 6.67/1.52  
% 6.67/1.52  
% 6.67/1.52  
% 6.67/1.52  ------ Proving...
% 6.67/1.52  
% 6.67/1.52  
% 6.67/1.52  % SZS status Theorem for theBenchmark.p
% 6.67/1.52  
% 6.67/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 6.67/1.52  
% 6.67/1.52  fof(f14,axiom,(
% 6.67/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f31,plain,(
% 6.67/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f14])).
% 6.67/1.52  
% 6.67/1.52  fof(f32,plain,(
% 6.67/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.67/1.52    inference(flattening,[],[f31])).
% 6.67/1.52  
% 6.67/1.52  fof(f56,plain,(
% 6.67/1.52    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.67/1.52    inference(cnf_transformation,[],[f32])).
% 6.67/1.52  
% 6.67/1.52  fof(f16,conjecture,(
% 6.67/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f17,negated_conjecture,(
% 6.67/1.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 6.67/1.52    inference(negated_conjecture,[],[f16])).
% 6.67/1.52  
% 6.67/1.52  fof(f34,plain,(
% 6.67/1.52    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f17])).
% 6.67/1.52  
% 6.67/1.52  fof(f35,plain,(
% 6.67/1.52    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.67/1.52    inference(flattening,[],[f34])).
% 6.67/1.52  
% 6.67/1.52  fof(f38,plain,(
% 6.67/1.52    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.67/1.52    inference(nnf_transformation,[],[f35])).
% 6.67/1.52  
% 6.67/1.52  fof(f39,plain,(
% 6.67/1.52    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.67/1.52    inference(flattening,[],[f38])).
% 6.67/1.52  
% 6.67/1.52  fof(f41,plain,(
% 6.67/1.52    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK2),sK2) != k2_tops_1(X0,sK2) | ~v3_pre_topc(sK2,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK2),sK2) = k2_tops_1(X0,sK2) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 6.67/1.52    introduced(choice_axiom,[])).
% 6.67/1.52  
% 6.67/1.52  fof(f40,plain,(
% 6.67/1.52    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) != k2_tops_1(sK1,X1) | ~v3_pre_topc(X1,sK1)) & (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) = k2_tops_1(sK1,X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 6.67/1.52    introduced(choice_axiom,[])).
% 6.67/1.52  
% 6.67/1.52  fof(f42,plain,(
% 6.67/1.52    ((k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1)) & (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 6.67/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).
% 6.67/1.52  
% 6.67/1.52  fof(f59,plain,(
% 6.67/1.52    v2_pre_topc(sK1)),
% 6.67/1.52    inference(cnf_transformation,[],[f42])).
% 6.67/1.52  
% 6.67/1.52  fof(f60,plain,(
% 6.67/1.52    l1_pre_topc(sK1)),
% 6.67/1.52    inference(cnf_transformation,[],[f42])).
% 6.67/1.52  
% 6.67/1.52  fof(f6,axiom,(
% 6.67/1.52    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f19,plain,(
% 6.67/1.52    ! [X0] : ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0))),
% 6.67/1.52    inference(pure_predicate_removal,[],[f6])).
% 6.67/1.52  
% 6.67/1.52  fof(f36,plain,(
% 6.67/1.52    ! [X0] : (? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 6.67/1.52    introduced(choice_axiom,[])).
% 6.67/1.52  
% 6.67/1.52  fof(f37,plain,(
% 6.67/1.52    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0))),
% 6.67/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).
% 6.67/1.52  
% 6.67/1.52  fof(f48,plain,(
% 6.67/1.52    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f37])).
% 6.67/1.52  
% 6.67/1.52  fof(f62,plain,(
% 6.67/1.52    k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) | v3_pre_topc(sK2,sK1)),
% 6.67/1.52    inference(cnf_transformation,[],[f42])).
% 6.67/1.52  
% 6.67/1.52  fof(f61,plain,(
% 6.67/1.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 6.67/1.52    inference(cnf_transformation,[],[f42])).
% 6.67/1.52  
% 6.67/1.52  fof(f11,axiom,(
% 6.67/1.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f27,plain,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f11])).
% 6.67/1.52  
% 6.67/1.52  fof(f28,plain,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 6.67/1.52    inference(flattening,[],[f27])).
% 6.67/1.52  
% 6.67/1.52  fof(f53,plain,(
% 6.67/1.52    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.67/1.52    inference(cnf_transformation,[],[f28])).
% 6.67/1.52  
% 6.67/1.52  fof(f7,axiom,(
% 6.67/1.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f24,plain,(
% 6.67/1.52    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f7])).
% 6.67/1.52  
% 6.67/1.52  fof(f49,plain,(
% 6.67/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f24])).
% 6.67/1.52  
% 6.67/1.52  fof(f1,axiom,(
% 6.67/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f43,plain,(
% 6.67/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f1])).
% 6.67/1.52  
% 6.67/1.52  fof(f9,axiom,(
% 6.67/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f51,plain,(
% 6.67/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f9])).
% 6.67/1.52  
% 6.67/1.52  fof(f64,plain,(
% 6.67/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 6.67/1.52    inference(definition_unfolding,[],[f43,f51])).
% 6.67/1.52  
% 6.67/1.52  fof(f66,plain,(
% 6.67/1.52    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(definition_unfolding,[],[f49,f64])).
% 6.67/1.52  
% 6.67/1.52  fof(f12,axiom,(
% 6.67/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f29,plain,(
% 6.67/1.52    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.67/1.52    inference(ennf_transformation,[],[f12])).
% 6.67/1.52  
% 6.67/1.52  fof(f54,plain,(
% 6.67/1.52    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.67/1.52    inference(cnf_transformation,[],[f29])).
% 6.67/1.52  
% 6.67/1.52  fof(f10,axiom,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f18,plain,(
% 6.67/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 6.67/1.52    inference(unused_predicate_definition_removal,[],[f10])).
% 6.67/1.52  
% 6.67/1.52  fof(f26,plain,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 6.67/1.52    inference(ennf_transformation,[],[f18])).
% 6.67/1.52  
% 6.67/1.52  fof(f52,plain,(
% 6.67/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.67/1.52    inference(cnf_transformation,[],[f26])).
% 6.67/1.52  
% 6.67/1.52  fof(f5,axiom,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f23,plain,(
% 6.67/1.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f5])).
% 6.67/1.52  
% 6.67/1.52  fof(f47,plain,(
% 6.67/1.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f23])).
% 6.67/1.52  
% 6.67/1.52  fof(f3,axiom,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f21,plain,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f3])).
% 6.67/1.52  
% 6.67/1.52  fof(f45,plain,(
% 6.67/1.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f21])).
% 6.67/1.52  
% 6.67/1.52  fof(f2,axiom,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f20,plain,(
% 6.67/1.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f2])).
% 6.67/1.52  
% 6.67/1.52  fof(f44,plain,(
% 6.67/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f20])).
% 6.67/1.52  
% 6.67/1.52  fof(f65,plain,(
% 6.67/1.52    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(definition_unfolding,[],[f44,f64])).
% 6.67/1.52  
% 6.67/1.52  fof(f8,axiom,(
% 6.67/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f25,plain,(
% 6.67/1.52    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f8])).
% 6.67/1.52  
% 6.67/1.52  fof(f50,plain,(
% 6.67/1.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f25])).
% 6.67/1.52  
% 6.67/1.52  fof(f4,axiom,(
% 6.67/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f22,plain,(
% 6.67/1.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.67/1.52    inference(ennf_transformation,[],[f4])).
% 6.67/1.52  
% 6.67/1.52  fof(f46,plain,(
% 6.67/1.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.67/1.52    inference(cnf_transformation,[],[f22])).
% 6.67/1.52  
% 6.67/1.52  fof(f15,axiom,(
% 6.67/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f33,plain,(
% 6.67/1.52    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.67/1.52    inference(ennf_transformation,[],[f15])).
% 6.67/1.52  
% 6.67/1.52  fof(f58,plain,(
% 6.67/1.52    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.67/1.52    inference(cnf_transformation,[],[f33])).
% 6.67/1.52  
% 6.67/1.52  fof(f13,axiom,(
% 6.67/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 6.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.52  
% 6.67/1.52  fof(f30,plain,(
% 6.67/1.52    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.67/1.52    inference(ennf_transformation,[],[f13])).
% 6.67/1.52  
% 6.67/1.52  fof(f55,plain,(
% 6.67/1.52    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.67/1.52    inference(cnf_transformation,[],[f30])).
% 6.67/1.52  
% 6.67/1.52  fof(f57,plain,(
% 6.67/1.52    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.67/1.52    inference(cnf_transformation,[],[f32])).
% 6.67/1.52  
% 6.67/1.52  fof(f63,plain,(
% 6.67/1.52    k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1)),
% 6.67/1.52    inference(cnf_transformation,[],[f42])).
% 6.67/1.52  
% 6.67/1.52  cnf(c_12,plain,
% 6.67/1.52      ( ~ v3_pre_topc(X0,X1)
% 6.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 6.67/1.52      | ~ v2_pre_topc(X3)
% 6.67/1.52      | ~ l1_pre_topc(X3)
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | k1_tops_1(X1,X0) = X0 ),
% 6.67/1.52      inference(cnf_transformation,[],[f56]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_226,plain,
% 6.67/1.52      ( sP1_iProver_split | sP0_iProver_split ),
% 6.67/1.52      inference(splitting,
% 6.67/1.52                [splitting(split),new_symbols(definition,[])],
% 6.67/1.52                [c_12]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_777,plain,
% 6.67/1.52      ( sP1_iProver_split = iProver_top
% 6.67/1.52      | sP0_iProver_split = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_18,negated_conjecture,
% 6.67/1.52      ( v2_pre_topc(sK1) ),
% 6.67/1.52      inference(cnf_transformation,[],[f59]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_19,plain,
% 6.67/1.52      ( v2_pre_topc(sK1) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_17,negated_conjecture,
% 6.67/1.52      ( l1_pre_topc(sK1) ),
% 6.67/1.52      inference(cnf_transformation,[],[f60]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_20,plain,
% 6.67/1.52      ( l1_pre_topc(sK1) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_269,plain,
% 6.67/1.52      ( sP1_iProver_split = iProver_top
% 6.67/1.52      | sP0_iProver_split = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_4,plain,
% 6.67/1.52      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 6.67/1.52      inference(cnf_transformation,[],[f48]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_789,plain,
% 6.67/1.52      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_224,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ v2_pre_topc(X1)
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | ~ sP0_iProver_split ),
% 6.67/1.52      inference(splitting,
% 6.67/1.52                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 6.67/1.52                [c_12]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_779,plain,
% 6.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 6.67/1.52      | v2_pre_topc(X1) != iProver_top
% 6.67/1.52      | l1_pre_topc(X1) != iProver_top
% 6.67/1.52      | sP0_iProver_split != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_2506,plain,
% 6.67/1.52      ( v2_pre_topc(X0) != iProver_top
% 6.67/1.52      | l1_pre_topc(X0) != iProver_top
% 6.67/1.52      | sP0_iProver_split != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_789,c_779]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_2527,plain,
% 6.67/1.52      ( v2_pre_topc(sK1) != iProver_top
% 6.67/1.52      | l1_pre_topc(sK1) != iProver_top
% 6.67/1.52      | sP0_iProver_split != iProver_top ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_2506]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_4181,plain,
% 6.67/1.52      ( sP1_iProver_split = iProver_top ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_777,c_19,c_20,c_269,c_2527]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_15,negated_conjecture,
% 6.67/1.52      ( v3_pre_topc(sK2,sK1)
% 6.67/1.52      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
% 6.67/1.52      inference(cnf_transformation,[],[f62]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_774,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
% 6.67/1.52      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_16,negated_conjecture,
% 6.67/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 6.67/1.52      inference(cnf_transformation,[],[f61]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_773,plain,
% 6.67/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_225,plain,
% 6.67/1.52      ( ~ v3_pre_topc(X0,X1)
% 6.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | k1_tops_1(X1,X0) = X0
% 6.67/1.52      | ~ sP1_iProver_split ),
% 6.67/1.52      inference(splitting,
% 6.67/1.52                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 6.67/1.52                [c_12]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_778,plain,
% 6.67/1.52      ( k1_tops_1(X0,X1) = X1
% 6.67/1.52      | v3_pre_topc(X1,X0) != iProver_top
% 6.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.67/1.52      | l1_pre_topc(X0) != iProver_top
% 6.67/1.52      | sP1_iProver_split != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1336,plain,
% 6.67/1.52      ( k1_tops_1(sK1,sK2) = sK2
% 6.67/1.52      | v3_pre_topc(sK2,sK1) != iProver_top
% 6.67/1.52      | l1_pre_topc(sK1) != iProver_top
% 6.67/1.52      | sP1_iProver_split != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_773,c_778]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_2085,plain,
% 6.67/1.52      ( v3_pre_topc(sK2,sK1) != iProver_top
% 6.67/1.52      | k1_tops_1(sK1,sK2) = sK2
% 6.67/1.52      | sP1_iProver_split != iProver_top ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_1336,c_20]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_2086,plain,
% 6.67/1.52      ( k1_tops_1(sK1,sK2) = sK2
% 6.67/1.52      | v3_pre_topc(sK2,sK1) != iProver_top
% 6.67/1.52      | sP1_iProver_split != iProver_top ),
% 6.67/1.52      inference(renaming,[status(thm)],[c_2085]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_2092,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
% 6.67/1.52      | k1_tops_1(sK1,sK2) = sK2
% 6.67/1.52      | sP1_iProver_split != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_774,c_2086]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_4186,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
% 6.67/1.52      | k1_tops_1(sK1,sK2) = sK2 ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_4181,c_2092]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_8,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ l1_pre_topc(X1) ),
% 6.67/1.52      inference(cnf_transformation,[],[f53]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_785,plain,
% 6.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 6.67/1.52      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 6.67/1.52      | l1_pre_topc(X1) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_5,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.67/1.52      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 6.67/1.52      inference(cnf_transformation,[],[f66]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_788,plain,
% 6.67/1.52      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 6.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_2797,plain,
% 6.67/1.52      ( k5_xboole_0(k2_pre_topc(X0,X1),k1_setfam_1(k2_tarski(k2_pre_topc(X0,X1),X2))) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2)
% 6.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.67/1.52      | l1_pre_topc(X0) != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_785,c_788]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_16439,plain,
% 6.67/1.52      ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0)
% 6.67/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_773,c_2797]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1023,plain,
% 6.67/1.52      ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 6.67/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 6.67/1.52      | ~ l1_pre_topc(sK1) ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_8]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1216,plain,
% 6.67/1.52      ( ~ m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 6.67/1.52      | k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_5]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_16581,plain,
% 6.67/1.52      ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_16439,c_17,c_16,c_1023,c_1216]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_9,plain,
% 6.67/1.52      ( r1_tarski(X0,k2_pre_topc(X1,X0))
% 6.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ l1_pre_topc(X1) ),
% 6.67/1.52      inference(cnf_transformation,[],[f54]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_784,plain,
% 6.67/1.52      ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 6.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 6.67/1.52      | l1_pre_topc(X1) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_2742,plain,
% 6.67/1.52      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
% 6.67/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_773,c_784]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_21,plain,
% 6.67/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1028,plain,
% 6.67/1.52      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2))
% 6.67/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 6.67/1.52      | ~ l1_pre_topc(sK1) ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_9]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1029,plain,
% 6.67/1.52      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
% 6.67/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 6.67/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_1028]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_3368,plain,
% 6.67/1.52      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_2742,c_20,c_21,c_1029]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_7,plain,
% 6.67/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.67/1.52      inference(cnf_transformation,[],[f52]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_786,plain,
% 6.67/1.52      ( r1_tarski(X0,X1) != iProver_top
% 6.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_3,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.67/1.52      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 6.67/1.52      inference(cnf_transformation,[],[f47]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_790,plain,
% 6.67/1.52      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 6.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1373,plain,
% 6.67/1.52      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 6.67/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_786,c_790]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_4320,plain,
% 6.67/1.52      ( k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = sK2 ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_3368,c_1373]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.67/1.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 6.67/1.52      inference(cnf_transformation,[],[f45]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_792,plain,
% 6.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.67/1.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_4548,plain,
% 6.67/1.52      ( m1_subset_1(k3_subset_1(k2_pre_topc(sK1,sK2),sK2),k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top
% 6.67/1.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_4320,c_792]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1285,plain,
% 6.67/1.52      ( ~ r1_tarski(sK2,k2_pre_topc(sK1,sK2))
% 6.67/1.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_7]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1286,plain,
% 6.67/1.52      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) != iProver_top
% 6.67/1.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_1285]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_5537,plain,
% 6.67/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_4548,c_20,c_21,c_1029,c_1286]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_0,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.67/1.52      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 6.67/1.52      inference(cnf_transformation,[],[f65]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_793,plain,
% 6.67/1.52      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 6.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_5543,plain,
% 6.67/1.52      ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),sK2))) = k3_subset_1(k2_pre_topc(sK1,sK2),sK2) ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_5537,c_793]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_16589,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k3_subset_1(k2_pre_topc(sK1,sK2),sK2) ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_16581,c_5543]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_16810,plain,
% 6.67/1.52      ( k1_tops_1(sK1,sK2) = sK2
% 6.67/1.52      | k3_subset_1(k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_4186,c_16589]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_6,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.67/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.67/1.52      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 6.67/1.52      inference(cnf_transformation,[],[f50]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_787,plain,
% 6.67/1.52      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 6.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.67/1.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_5542,plain,
% 6.67/1.52      ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0)) = k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0)
% 6.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_5537,c_787]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_5545,plain,
% 6.67/1.52      ( k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_5537,c_788]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1904,plain,
% 6.67/1.52      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_773,c_788]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_5547,plain,
% 6.67/1.52      ( k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
% 6.67/1.52      inference(light_normalisation,[status(thm)],[c_5545,c_1904]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_5551,plain,
% 6.67/1.52      ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0)) = k7_subset_1(u1_struct_0(sK1),sK2,X0)
% 6.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
% 6.67/1.52      inference(light_normalisation,[status(thm)],[c_5542,c_5547]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_6611,plain,
% 6.67/1.52      ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0))
% 6.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_792,c_5551]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_10609,plain,
% 6.67/1.52      ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),sK2))) = k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_5537,c_6611]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_10611,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = k9_subset_1(k2_pre_topc(sK1,sK2),sK2,sK2) ),
% 6.67/1.52      inference(light_normalisation,[status(thm)],[c_10609,c_4320]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_2,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 6.67/1.52      inference(cnf_transformation,[],[f46]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_791,plain,
% 6.67/1.52      ( k9_subset_1(X0,X1,X1) = X1
% 6.67/1.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_995,plain,
% 6.67/1.52      ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(X0))
% 6.67/1.52      | k9_subset_1(X0,X1,X1) = X1 ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1190,plain,
% 6.67/1.52      ( k9_subset_1(X0,X1,X1) = X1 ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_791,c_4,c_995]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_10612,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = sK2 ),
% 6.67/1.52      inference(demodulation,[status(thm)],[c_10611,c_1190]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_16913,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = sK2
% 6.67/1.52      | k1_tops_1(sK1,sK2) = sK2 ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_16810,c_10612]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_13,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 6.67/1.52      inference(cnf_transformation,[],[f58]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_776,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 6.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.67/1.52      | l1_pre_topc(X0) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_3159,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2)
% 6.67/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_773,c_776]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1119,plain,
% 6.67/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 6.67/1.52      | ~ l1_pre_topc(sK1)
% 6.67/1.52      | k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_13]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_3522,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_3159,c_17,c_16,c_1119]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_16937,plain,
% 6.67/1.52      ( k1_tops_1(sK1,sK2) = sK2 ),
% 6.67/1.52      inference(demodulation,[status(thm)],[c_16913,c_3522]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_10,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 6.67/1.52      inference(cnf_transformation,[],[f55]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_783,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 6.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.67/1.52      | l1_pre_topc(X0) != iProver_top ),
% 6.67/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_4008,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 6.67/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 6.67/1.52      inference(superposition,[status(thm)],[c_773,c_783]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1129,plain,
% 6.67/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 6.67/1.52      | ~ l1_pre_topc(sK1)
% 6.67/1.52      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_4322,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_4008,c_17,c_16,c_1129]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_16962,plain,
% 6.67/1.52      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
% 6.67/1.52      inference(demodulation,[status(thm)],[c_16937,c_4322]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_11,plain,
% 6.67/1.52      ( v3_pre_topc(X0,X1)
% 6.67/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 6.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ v2_pre_topc(X1)
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | ~ l1_pre_topc(X3)
% 6.67/1.52      | k1_tops_1(X1,X0) != X0 ),
% 6.67/1.52      inference(cnf_transformation,[],[f57]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_228,plain,
% 6.67/1.52      ( v3_pre_topc(X0,X1)
% 6.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ v2_pre_topc(X1)
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | k1_tops_1(X1,X0) != X0
% 6.67/1.52      | ~ sP3_iProver_split ),
% 6.67/1.52      inference(splitting,
% 6.67/1.52                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 6.67/1.52                [c_11]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_229,plain,
% 6.67/1.52      ( sP3_iProver_split | sP2_iProver_split ),
% 6.67/1.52      inference(splitting,
% 6.67/1.52                [splitting(split),new_symbols(definition,[])],
% 6.67/1.52                [c_11]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_227,plain,
% 6.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | ~ sP2_iProver_split ),
% 6.67/1.52      inference(splitting,
% 6.67/1.52                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 6.67/1.52                [c_11]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_483,plain,
% 6.67/1.52      ( k1_tops_1(X1,X0) != X0
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | ~ v2_pre_topc(X1)
% 6.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | v3_pre_topc(X0,X1) ),
% 6.67/1.52      inference(global_propositional_subsumption,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_228,c_229,c_227]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_484,plain,
% 6.67/1.52      ( v3_pre_topc(X0,X1)
% 6.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.67/1.52      | ~ v2_pre_topc(X1)
% 6.67/1.52      | ~ l1_pre_topc(X1)
% 6.67/1.52      | k1_tops_1(X1,X0) != X0 ),
% 6.67/1.52      inference(renaming,[status(thm)],[c_483]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_1124,plain,
% 6.67/1.52      ( v3_pre_topc(sK2,sK1)
% 6.67/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 6.67/1.52      | ~ v2_pre_topc(sK1)
% 6.67/1.52      | ~ l1_pre_topc(sK1)
% 6.67/1.52      | k1_tops_1(sK1,sK2) != sK2 ),
% 6.67/1.52      inference(instantiation,[status(thm)],[c_484]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(c_14,negated_conjecture,
% 6.67/1.52      ( ~ v3_pre_topc(sK2,sK1)
% 6.67/1.52      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2) ),
% 6.67/1.52      inference(cnf_transformation,[],[f63]) ).
% 6.67/1.52  
% 6.67/1.52  cnf(contradiction,plain,
% 6.67/1.52      ( $false ),
% 6.67/1.52      inference(minisat,
% 6.67/1.52                [status(thm)],
% 6.67/1.52                [c_16962,c_16937,c_1124,c_14,c_16,c_17,c_18]) ).
% 6.67/1.52  
% 6.67/1.52  
% 6.67/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 6.67/1.52  
% 6.67/1.52  ------                               Statistics
% 6.67/1.52  
% 6.67/1.52  ------ Selected
% 6.67/1.52  
% 6.67/1.52  total_time:                             0.594
% 6.67/1.52  
%------------------------------------------------------------------------------
