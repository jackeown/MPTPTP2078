%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:25 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  162 (1515 expanded)
%              Number of clauses        :   97 ( 445 expanded)
%              Number of leaves         :   19 ( 326 expanded)
%              Depth                    :   24
%              Number of atoms          :  432 (6600 expanded)
%              Number of equality atoms :  188 (1947 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2)
      | ~ v3_pre_topc(sK2,sK1) )
    & ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).

fof(f65,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f38])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
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

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f67])).

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

fof(f56,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f67])).

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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_804,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_803,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_238,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_13])).

cnf(c_808,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_2520,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | v3_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_808])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_239,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_13])).

cnf(c_282,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_13])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2582,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_237,c_2])).

cnf(c_2583,plain,
    ( v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2582])).

cnf(c_2585,plain,
    ( v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_2583])).

cnf(c_3489,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2520,c_20,c_21,c_282,c_2585])).

cnf(c_3495,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | k1_tops_1(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_804,c_3489])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_816,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_820,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2810,plain,
    ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_820])).

cnf(c_16581,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_2810])).

cnf(c_1057,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1255,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_16774,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16581,c_18,c_17,c_1057,c_1255])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_823,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16781,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16774,c_823])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1058,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_16808,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16781,c_21,c_22,c_1058])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_819,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16832,plain,
    ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_16808,c_819])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_815,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2774,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_815])).

cnf(c_1062,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1063,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_3348,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2774,c_21,c_22,c_1063])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_817,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_824,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1612,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_824])).

cnf(c_4473,plain,
    ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),sK2))) = k3_subset_1(k2_pre_topc(sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_3348,c_1612])).

cnf(c_17619,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k3_subset_1(k2_pre_topc(sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_16832,c_4473])).

cnf(c_18520,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | k3_subset_1(k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3495,c_17619])).

cnf(c_1375,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_820])).

cnf(c_3353,plain,
    ( k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3348,c_1375])).

cnf(c_3953,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK1,sK2),sK2),k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3353,c_823])).

cnf(c_1327,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK1,sK2))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1328,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_6288,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3953,c_21,c_22,c_1063,c_1328])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_818,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6293,plain,
    ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0)) = k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6288,c_818])).

cnf(c_1774,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_819])).

cnf(c_5880,plain,
    ( k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_3348,c_1774])).

cnf(c_1777,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(superposition,[status(thm)],[c_803,c_819])).

cnf(c_5881,plain,
    ( k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_5880,c_1777])).

cnf(c_6299,plain,
    ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0)) = k7_subset_1(u1_struct_0(sK1),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6293,c_5881])).

cnf(c_6655,plain,
    ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_6299])).

cnf(c_11588,plain,
    ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),sK2))) = k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_6288,c_6655])).

cnf(c_11590,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = k9_subset_1(k2_pre_topc(sK1,sK2),sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_11588,c_3353])).

cnf(c_822,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_821,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1224,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(superposition,[status(thm)],[c_822,c_821])).

cnf(c_11591,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_11590,c_1224])).

cnf(c_18751,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = sK2
    | k1_tops_1(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_18520,c_11591])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_806,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1350,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_806])).

cnf(c_1150,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2112,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1350,c_18,c_17,c_1150])).

cnf(c_18775,plain,
    ( k1_tops_1(sK1,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_18751,c_2112])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_813,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3213,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_813])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3355,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3213,c_18,c_17,c_1160])).

cnf(c_18779,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_18775,c_3355])).

cnf(c_12,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_241,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_12])).

cnf(c_242,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_12])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_12])).

cnf(c_503,plain,
    ( k1_tops_1(X1,X0) != X0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_241,c_242,c_240])).

cnf(c_504,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_503])).

cnf(c_1155,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18779,c_18775,c_1155,c_15,c_17,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.68/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.68/1.49  
% 7.68/1.49  ------  iProver source info
% 7.68/1.49  
% 7.68/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.68/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.68/1.49  git: non_committed_changes: false
% 7.68/1.49  git: last_make_outside_of_git: false
% 7.68/1.49  
% 7.68/1.49  ------ 
% 7.68/1.49  ------ Parsing...
% 7.68/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  ------ Proving...
% 7.68/1.49  ------ Problem Properties 
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  clauses                                 24
% 7.68/1.49  conjectures                             5
% 7.68/1.49  EPR                                     4
% 7.68/1.49  Horn                                    21
% 7.68/1.49  unary                                   4
% 7.68/1.49  binary                                  10
% 7.68/1.49  lits                                    61
% 7.68/1.49  lits eq                                 11
% 7.68/1.49  fd_pure                                 0
% 7.68/1.49  fd_pseudo                               0
% 7.68/1.49  fd_cond                                 0
% 7.68/1.49  fd_pseudo_cond                          0
% 7.68/1.49  AC symbols                              0
% 7.68/1.49  
% 7.68/1.49  ------ Input Options Time Limit: Unbounded
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ 
% 7.68/1.49  Current options:
% 7.68/1.49  ------ 
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  % SZS status Theorem for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  fof(f17,conjecture,(
% 7.68/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f18,negated_conjecture,(
% 7.68/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 7.68/1.49    inference(negated_conjecture,[],[f17])).
% 7.68/1.49  
% 7.68/1.49  fof(f36,plain,(
% 7.68/1.49    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f18])).
% 7.68/1.49  
% 7.68/1.49  fof(f37,plain,(
% 7.68/1.49    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.68/1.49    inference(flattening,[],[f36])).
% 7.68/1.49  
% 7.68/1.49  fof(f40,plain,(
% 7.68/1.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.68/1.49    inference(nnf_transformation,[],[f37])).
% 7.68/1.49  
% 7.68/1.49  fof(f41,plain,(
% 7.68/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.68/1.49    inference(flattening,[],[f40])).
% 7.68/1.49  
% 7.68/1.49  fof(f43,plain,(
% 7.68/1.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK2),sK2) != k2_tops_1(X0,sK2) | ~v3_pre_topc(sK2,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK2),sK2) = k2_tops_1(X0,sK2) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.68/1.49    introduced(choice_axiom,[])).
% 7.68/1.49  
% 7.68/1.49  fof(f42,plain,(
% 7.68/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) != k2_tops_1(sK1,X1) | ~v3_pre_topc(X1,sK1)) & (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) = k2_tops_1(sK1,X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 7.68/1.49    introduced(choice_axiom,[])).
% 7.68/1.49  
% 7.68/1.49  fof(f44,plain,(
% 7.68/1.49    ((k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1)) & (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 7.68/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).
% 7.68/1.49  
% 7.68/1.49  fof(f65,plain,(
% 7.68/1.49    k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) | v3_pre_topc(sK2,sK1)),
% 7.68/1.49    inference(cnf_transformation,[],[f44])).
% 7.68/1.49  
% 7.68/1.49  fof(f64,plain,(
% 7.68/1.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.68/1.49    inference(cnf_transformation,[],[f44])).
% 7.68/1.49  
% 7.68/1.49  fof(f15,axiom,(
% 7.68/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f33,plain,(
% 7.68/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f15])).
% 7.68/1.49  
% 7.68/1.49  fof(f34,plain,(
% 7.68/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.68/1.49    inference(flattening,[],[f33])).
% 7.68/1.49  
% 7.68/1.49  fof(f59,plain,(
% 7.68/1.49    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f34])).
% 7.68/1.49  
% 7.68/1.49  fof(f62,plain,(
% 7.68/1.49    v2_pre_topc(sK1)),
% 7.68/1.49    inference(cnf_transformation,[],[f44])).
% 7.68/1.49  
% 7.68/1.49  fof(f63,plain,(
% 7.68/1.49    l1_pre_topc(sK1)),
% 7.68/1.49    inference(cnf_transformation,[],[f44])).
% 7.68/1.49  
% 7.68/1.49  fof(f4,axiom,(
% 7.68/1.49    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f38,plain,(
% 7.68/1.49    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 7.68/1.49    introduced(choice_axiom,[])).
% 7.68/1.49  
% 7.68/1.49  fof(f39,plain,(
% 7.68/1.49    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 7.68/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f38])).
% 7.68/1.49  
% 7.68/1.49  fof(f48,plain,(
% 7.68/1.49    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f39])).
% 7.68/1.49  
% 7.68/1.49  fof(f11,axiom,(
% 7.68/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f27,plain,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f11])).
% 7.68/1.49  
% 7.68/1.49  fof(f28,plain,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.68/1.49    inference(flattening,[],[f27])).
% 7.68/1.49  
% 7.68/1.49  fof(f55,plain,(
% 7.68/1.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f28])).
% 7.68/1.49  
% 7.68/1.49  fof(f6,axiom,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f23,plain,(
% 7.68/1.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f6])).
% 7.68/1.49  
% 7.68/1.49  fof(f50,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f23])).
% 7.68/1.49  
% 7.68/1.49  fof(f3,axiom,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f21,plain,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f3])).
% 7.68/1.49  
% 7.68/1.49  fof(f47,plain,(
% 7.68/1.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f21])).
% 7.68/1.49  
% 7.68/1.49  fof(f7,axiom,(
% 7.68/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f24,plain,(
% 7.68/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f7])).
% 7.68/1.49  
% 7.68/1.49  fof(f51,plain,(
% 7.68/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f24])).
% 7.68/1.49  
% 7.68/1.49  fof(f1,axiom,(
% 7.68/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f45,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f1])).
% 7.68/1.49  
% 7.68/1.49  fof(f9,axiom,(
% 7.68/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f53,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f9])).
% 7.68/1.49  
% 7.68/1.49  fof(f67,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.68/1.49    inference(definition_unfolding,[],[f45,f53])).
% 7.68/1.49  
% 7.68/1.49  fof(f69,plain,(
% 7.68/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.68/1.49    inference(definition_unfolding,[],[f51,f67])).
% 7.68/1.49  
% 7.68/1.49  fof(f12,axiom,(
% 7.68/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f29,plain,(
% 7.68/1.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.68/1.49    inference(ennf_transformation,[],[f12])).
% 7.68/1.49  
% 7.68/1.49  fof(f56,plain,(
% 7.68/1.49    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f29])).
% 7.68/1.49  
% 7.68/1.49  fof(f10,axiom,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f19,plain,(
% 7.68/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.68/1.49    inference(unused_predicate_definition_removal,[],[f10])).
% 7.68/1.49  
% 7.68/1.49  fof(f26,plain,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.68/1.49    inference(ennf_transformation,[],[f19])).
% 7.68/1.49  
% 7.68/1.49  fof(f54,plain,(
% 7.68/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f26])).
% 7.68/1.49  
% 7.68/1.49  fof(f2,axiom,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f20,plain,(
% 7.68/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f2])).
% 7.68/1.49  
% 7.68/1.49  fof(f46,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f20])).
% 7.68/1.49  
% 7.68/1.49  fof(f68,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.68/1.49    inference(definition_unfolding,[],[f46,f67])).
% 7.68/1.49  
% 7.68/1.49  fof(f8,axiom,(
% 7.68/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f25,plain,(
% 7.68/1.49    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f8])).
% 7.68/1.49  
% 7.68/1.49  fof(f52,plain,(
% 7.68/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f25])).
% 7.68/1.49  
% 7.68/1.49  fof(f5,axiom,(
% 7.68/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f22,plain,(
% 7.68/1.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f5])).
% 7.68/1.49  
% 7.68/1.49  fof(f49,plain,(
% 7.68/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f22])).
% 7.68/1.49  
% 7.68/1.49  fof(f16,axiom,(
% 7.68/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f35,plain,(
% 7.68/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.68/1.49    inference(ennf_transformation,[],[f16])).
% 7.68/1.49  
% 7.68/1.49  fof(f61,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f35])).
% 7.68/1.49  
% 7.68/1.49  fof(f14,axiom,(
% 7.68/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f32,plain,(
% 7.68/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.68/1.49    inference(ennf_transformation,[],[f14])).
% 7.68/1.49  
% 7.68/1.49  fof(f58,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f32])).
% 7.68/1.49  
% 7.68/1.49  fof(f60,plain,(
% 7.68/1.49    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f34])).
% 7.68/1.49  
% 7.68/1.49  fof(f66,plain,(
% 7.68/1.49    k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1)),
% 7.68/1.49    inference(cnf_transformation,[],[f44])).
% 7.68/1.49  
% 7.68/1.49  cnf(c_16,negated_conjecture,
% 7.68/1.49      ( v3_pre_topc(sK2,sK1)
% 7.68/1.49      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
% 7.68/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_804,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
% 7.68/1.49      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_17,negated_conjecture,
% 7.68/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.68/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_803,plain,
% 7.68/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_13,plain,
% 7.68/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.68/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.68/1.49      | ~ v2_pre_topc(X3)
% 7.68/1.49      | ~ l1_pre_topc(X3)
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | k1_tops_1(X1,X0) = X0 ),
% 7.68/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_238,plain,
% 7.68/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.68/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | k1_tops_1(X1,X0) = X0
% 7.68/1.49      | ~ sP1_iProver_split ),
% 7.68/1.49      inference(splitting,
% 7.68/1.49                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.68/1.49                [c_13]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_808,plain,
% 7.68/1.49      ( k1_tops_1(X0,X1) = X1
% 7.68/1.49      | v3_pre_topc(X1,X0) != iProver_top
% 7.68/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.68/1.49      | l1_pre_topc(X0) != iProver_top
% 7.68/1.49      | sP1_iProver_split != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_238]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2520,plain,
% 7.68/1.49      ( k1_tops_1(sK1,sK2) = sK2
% 7.68/1.49      | v3_pre_topc(sK2,sK1) != iProver_top
% 7.68/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.68/1.49      | sP1_iProver_split != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_803,c_808]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_19,negated_conjecture,
% 7.68/1.49      ( v2_pre_topc(sK1) ),
% 7.68/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_20,plain,
% 7.68/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_18,negated_conjecture,
% 7.68/1.49      ( l1_pre_topc(sK1) ),
% 7.68/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_21,plain,
% 7.68/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_239,plain,
% 7.68/1.49      ( sP1_iProver_split | sP0_iProver_split ),
% 7.68/1.49      inference(splitting,
% 7.68/1.49                [splitting(split),new_symbols(definition,[])],
% 7.68/1.49                [c_13]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_282,plain,
% 7.68/1.49      ( sP1_iProver_split = iProver_top
% 7.68/1.49      | sP0_iProver_split = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_237,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ v2_pre_topc(X1)
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | ~ sP0_iProver_split ),
% 7.68/1.49      inference(splitting,
% 7.68/1.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.68/1.49                [c_13]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2,plain,
% 7.68/1.49      ( m1_subset_1(sK0(X0),X0) ),
% 7.68/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2582,plain,
% 7.68/1.49      ( ~ v2_pre_topc(X0) | ~ l1_pre_topc(X0) | ~ sP0_iProver_split ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_237,c_2]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2583,plain,
% 7.68/1.49      ( v2_pre_topc(X0) != iProver_top
% 7.68/1.49      | l1_pre_topc(X0) != iProver_top
% 7.68/1.49      | sP0_iProver_split != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_2582]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2585,plain,
% 7.68/1.49      ( v2_pre_topc(sK1) != iProver_top
% 7.68/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.68/1.49      | sP0_iProver_split != iProver_top ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_2583]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3489,plain,
% 7.68/1.49      ( k1_tops_1(sK1,sK2) = sK2 | v3_pre_topc(sK2,sK1) != iProver_top ),
% 7.68/1.49      inference(global_propositional_subsumption,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_2520,c_20,c_21,c_282,c_2585]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3495,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
% 7.68/1.49      | k1_tops_1(sK1,sK2) = sK2 ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_804,c_3489]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_8,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ l1_pre_topc(X1) ),
% 7.68/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_816,plain,
% 7.68/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.68/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.68/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_4,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.68/1.49      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.68/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_820,plain,
% 7.68/1.49      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.68/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2810,plain,
% 7.68/1.49      ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))) = k2_pre_topc(X0,X1)
% 7.68/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.68/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_816,c_820]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_16581,plain,
% 7.68/1.49      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,sK2)
% 7.68/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_803,c_2810]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1057,plain,
% 7.68/1.49      ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.68/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.68/1.49      | ~ l1_pre_topc(sK1) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1255,plain,
% 7.68/1.49      ( ~ m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.68/1.49      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,sK2) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_16774,plain,
% 7.68/1.49      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,sK2) ),
% 7.68/1.49      inference(global_propositional_subsumption,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_16581,c_18,c_17,c_1057,c_1255]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.68/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.68/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_823,plain,
% 7.68/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.68/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_16781,plain,
% 7.68/1.49      ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.68/1.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_16774,c_823]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_22,plain,
% 7.68/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1058,plain,
% 7.68/1.49      ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.68/1.49      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.68/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_16808,plain,
% 7.68/1.49      ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.68/1.49      inference(global_propositional_subsumption,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_16781,c_21,c_22,c_1058]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_5,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.68/1.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 7.68/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_819,plain,
% 7.68/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 7.68/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_16832,plain,
% 7.68/1.49      ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_16808,c_819]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_9,plain,
% 7.68/1.49      ( r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.68/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ l1_pre_topc(X1) ),
% 7.68/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_815,plain,
% 7.68/1.49      ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 7.68/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.68/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2774,plain,
% 7.68/1.49      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
% 7.68/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_803,c_815]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1062,plain,
% 7.68/1.49      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2))
% 7.68/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.68/1.49      | ~ l1_pre_topc(sK1) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1063,plain,
% 7.68/1.49      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
% 7.68/1.49      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.68/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_1062]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3348,plain,
% 7.68/1.49      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top ),
% 7.68/1.49      inference(global_propositional_subsumption,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_2774,c_21,c_22,c_1063]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_7,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.68/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_817,plain,
% 7.68/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.68/1.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_0,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.68/1.49      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 7.68/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_824,plain,
% 7.68/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 7.68/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1612,plain,
% 7.68/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 7.68/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_817,c_824]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_4473,plain,
% 7.68/1.49      ( k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),sK2))) = k3_subset_1(k2_pre_topc(sK1,sK2),sK2) ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_3348,c_1612]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_17619,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k3_subset_1(k2_pre_topc(sK1,sK2),sK2) ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_16832,c_4473]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_18520,plain,
% 7.68/1.49      ( k1_tops_1(sK1,sK2) = sK2
% 7.68/1.49      | k3_subset_1(k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_3495,c_17619]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1375,plain,
% 7.68/1.49      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.68/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_817,c_820]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3353,plain,
% 7.68/1.49      ( k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = sK2 ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_3348,c_1375]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3953,plain,
% 7.68/1.49      ( m1_subset_1(k3_subset_1(k2_pre_topc(sK1,sK2),sK2),k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top
% 7.68/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_3353,c_823]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1327,plain,
% 7.68/1.49      ( ~ r1_tarski(sK2,k2_pre_topc(sK1,sK2))
% 7.68/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1328,plain,
% 7.68/1.49      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) != iProver_top
% 7.68/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_1327]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_6288,plain,
% 7.68/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) = iProver_top ),
% 7.68/1.49      inference(global_propositional_subsumption,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_3953,c_21,c_22,c_1063,c_1328]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_6,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.68/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.68/1.49      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.68/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_818,plain,
% 7.68/1.49      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 7.68/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.68/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_6293,plain,
% 7.68/1.49      ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0)) = k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0)
% 7.68/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_6288,c_818]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1774,plain,
% 7.68/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 7.68/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_817,c_819]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_5880,plain,
% 7.68/1.49      ( k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_3348,c_1774]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1777,plain,
% 7.68/1.49      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_803,c_819]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_5881,plain,
% 7.68/1.49      ( k7_subset_1(k2_pre_topc(sK1,sK2),sK2,X0) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
% 7.68/1.49      inference(light_normalisation,[status(thm)],[c_5880,c_1777]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_6299,plain,
% 7.68/1.49      ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0)) = k7_subset_1(u1_struct_0(sK1),sK2,X0)
% 7.68/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
% 7.68/1.49      inference(light_normalisation,[status(thm)],[c_6293,c_5881]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_6655,plain,
% 7.68/1.49      ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),X0))) = k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),X0))
% 7.68/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK1,sK2))) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_823,c_6299]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_11588,plain,
% 7.68/1.49      ( k9_subset_1(k2_pre_topc(sK1,sK2),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),k3_subset_1(k2_pre_topc(sK1,sK2),sK2))) = k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_6288,c_6655]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_11590,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = k9_subset_1(k2_pre_topc(sK1,sK2),sK2,sK2) ),
% 7.68/1.49      inference(light_normalisation,[status(thm)],[c_11588,c_3353]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_822,plain,
% 7.68/1.49      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 7.68/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_821,plain,
% 7.68/1.49      ( k9_subset_1(X0,X1,X1) = X1
% 7.68/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1224,plain,
% 7.68/1.49      ( k9_subset_1(X0,X1,X1) = X1 ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_822,c_821]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_11591,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k3_subset_1(k2_pre_topc(sK1,sK2),sK2)) = sK2 ),
% 7.68/1.49      inference(demodulation,[status(thm)],[c_11590,c_1224]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_18751,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = sK2
% 7.68/1.49      | k1_tops_1(sK1,sK2) = sK2 ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_18520,c_11591]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_14,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 7.68/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_806,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 7.68/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.68/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1350,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2)
% 7.68/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_803,c_806]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1150,plain,
% 7.68/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.68/1.49      | ~ l1_pre_topc(sK1)
% 7.68/1.49      | k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2112,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
% 7.68/1.49      inference(global_propositional_subsumption,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_1350,c_18,c_17,c_1150]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_18775,plain,
% 7.68/1.49      ( k1_tops_1(sK1,sK2) = sK2 ),
% 7.68/1.49      inference(demodulation,[status(thm)],[c_18751,c_2112]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_11,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.68/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_813,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.68/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.68/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3213,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 7.68/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_803,c_813]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1160,plain,
% 7.68/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.68/1.49      | ~ l1_pre_topc(sK1)
% 7.68/1.49      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3355,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 7.68/1.49      inference(global_propositional_subsumption,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_3213,c_18,c_17,c_1160]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_18779,plain,
% 7.68/1.49      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
% 7.68/1.49      inference(demodulation,[status(thm)],[c_18775,c_3355]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_12,plain,
% 7.68/1.49      ( v3_pre_topc(X0,X1)
% 7.68/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.68/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ v2_pre_topc(X1)
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | ~ l1_pre_topc(X3)
% 7.68/1.49      | k1_tops_1(X1,X0) != X0 ),
% 7.68/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_241,plain,
% 7.68/1.49      ( v3_pre_topc(X0,X1)
% 7.68/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ v2_pre_topc(X1)
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | k1_tops_1(X1,X0) != X0
% 7.68/1.49      | ~ sP3_iProver_split ),
% 7.68/1.49      inference(splitting,
% 7.68/1.49                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 7.68/1.49                [c_12]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_242,plain,
% 7.68/1.49      ( sP3_iProver_split | sP2_iProver_split ),
% 7.68/1.49      inference(splitting,
% 7.68/1.49                [splitting(split),new_symbols(definition,[])],
% 7.68/1.49                [c_12]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_240,plain,
% 7.68/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | ~ sP2_iProver_split ),
% 7.68/1.49      inference(splitting,
% 7.68/1.49                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 7.68/1.49                [c_12]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_503,plain,
% 7.68/1.49      ( k1_tops_1(X1,X0) != X0
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | ~ v2_pre_topc(X1)
% 7.68/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | v3_pre_topc(X0,X1) ),
% 7.68/1.49      inference(global_propositional_subsumption,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_241,c_242,c_240]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_504,plain,
% 7.68/1.49      ( v3_pre_topc(X0,X1)
% 7.68/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.68/1.49      | ~ v2_pre_topc(X1)
% 7.68/1.49      | ~ l1_pre_topc(X1)
% 7.68/1.49      | k1_tops_1(X1,X0) != X0 ),
% 7.68/1.49      inference(renaming,[status(thm)],[c_503]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1155,plain,
% 7.68/1.49      ( v3_pre_topc(sK2,sK1)
% 7.68/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.68/1.49      | ~ v2_pre_topc(sK1)
% 7.68/1.49      | ~ l1_pre_topc(sK1)
% 7.68/1.49      | k1_tops_1(sK1,sK2) != sK2 ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_504]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_15,negated_conjecture,
% 7.68/1.49      ( ~ v3_pre_topc(sK2,sK1)
% 7.68/1.49      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) != k2_tops_1(sK1,sK2) ),
% 7.68/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(contradiction,plain,
% 7.68/1.49      ( $false ),
% 7.68/1.49      inference(minisat,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_18779,c_18775,c_1155,c_15,c_17,c_18,c_19]) ).
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  ------                               Statistics
% 7.68/1.49  
% 7.68/1.49  ------ Selected
% 7.68/1.49  
% 7.68/1.49  total_time:                             0.548
% 7.68/1.49  
%------------------------------------------------------------------------------
