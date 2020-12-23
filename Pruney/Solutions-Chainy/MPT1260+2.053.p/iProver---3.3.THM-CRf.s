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
% DateTime   : Thu Dec  3 12:14:22 EST 2020

% Result     : Theorem 23.58s
% Output     : CNFRefutation 23.58s
% Verified   : 
% Statistics : Number of formulae       :  221 (3050 expanded)
%              Number of clauses        :  159 (1144 expanded)
%              Number of leaves         :   21 ( 604 expanded)
%              Depth                    :   23
%              Number of atoms          :  566 (12017 expanded)
%              Number of equality atoms :  299 (3651 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) != k2_tops_1(X0,sK1)
          | ~ v3_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) = k2_tops_1(X0,sK1)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
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
          ( ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) != k2_tops_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) = k2_tops_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f49,f55,f55])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1139,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1152,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6592,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_1153])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_177,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_178,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_228,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_178])).

cnf(c_1134,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_27642,plain,
    ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6592,c_1134])).

cnf(c_64509,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_27642])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_226,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_178])).

cnf(c_1136,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_27641,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1)) = k4_xboole_0(u1_struct_0(X0),k2_pre_topc(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6592,c_1136])).

cnf(c_61331,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_27641])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_62880,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61331,c_28])).

cnf(c_64512,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_64509,c_62880])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1156,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5571,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1156,c_1136])).

cnf(c_64513,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_64512,c_5571])).

cnf(c_65268,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_64513,c_28])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_229,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_178])).

cnf(c_1133,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_42906,plain,
    ( k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1156,c_1133])).

cnf(c_65274,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_65268,c_42906])).

cnf(c_65542,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_65274,c_65268])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1140,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2258,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1153])).

cnf(c_1154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_492,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_20])).

cnf(c_1144,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_2474,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1144])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_493,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_20])).

cnf(c_540,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1155,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_20])).

cnf(c_1145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_3962,plain,
    ( v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1145])).

cnf(c_3983,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3962])).

cnf(c_16774,plain,
    ( l1_pre_topc(X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | k1_tops_1(X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2474,c_27,c_28,c_540,c_3983])).

cnf(c_16775,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16774])).

cnf(c_16787,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | v3_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2258,c_16775])).

cnf(c_2476,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | v3_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1144])).

cnf(c_18521,plain,
    ( v3_pre_topc(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16787,c_27,c_28,c_540,c_2476,c_3983])).

cnf(c_18522,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18521])).

cnf(c_18527,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1140,c_18522])).

cnf(c_78920,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_65542,c_18527])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4343,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1151])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1412,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_4362,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4343,c_28,c_29,c_1412])).

cnf(c_5574,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_4362,c_1136])).

cnf(c_4367,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_4362,c_1134])).

cnf(c_5725,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_5574,c_4367])).

cnf(c_80950,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_78920,c_5725])).

cnf(c_2509,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP1_iProver_split
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2476])).

cnf(c_3982,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3962])).

cnf(c_3984,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_3982])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_498,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4478,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_504,c_498])).

cnf(c_499,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2821,plain,
    ( X0 != X1
    | k4_xboole_0(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_499,c_5])).

cnf(c_10284,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k4_xboole_0(X2,k1_xboole_0),X1)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_4478,c_2821])).

cnf(c_84514,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1),X0)
    | m1_subset_1(k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_10284,c_23])).

cnf(c_4458,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k4_xboole_0(X1,k1_xboole_0))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_504,c_5])).

cnf(c_16551,plain,
    ( v3_pre_topc(sK1,sK0)
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1),k4_xboole_0(X0,k1_xboole_0))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),X0) ),
    inference(resolution,[status(thm)],[c_4458,c_23])).

cnf(c_86280,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),X0)
    | m1_subset_1(k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_84514,c_16551])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1558,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1559,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1142,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1568,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1142])).

cnf(c_1471,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1944,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1568,c_25,c_24,c_1471])).

cnf(c_42910,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2258,c_1133])).

cnf(c_43165,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1944,c_42910])).

cnf(c_43181,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_43165,c_1156])).

cnf(c_5573,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_2258,c_1136])).

cnf(c_3615,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_2258,c_1134])).

cnf(c_5723,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_5573,c_3615])).

cnf(c_6172,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_5571,c_5723])).

cnf(c_1138,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1776,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1156])).

cnf(c_2336,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1142])).

cnf(c_14915,plain,
    ( k7_subset_1(u1_struct_0(X0),k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))),k2_tops_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))))) = k1_tops_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_2336])).

cnf(c_50939,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k2_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))))) = k1_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))) ),
    inference(superposition,[status(thm)],[c_1138,c_14915])).

cnf(c_14912,plain,
    ( k7_subset_1(u1_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1),k2_tops_1(X0,k4_xboole_0(u1_struct_0(X0),X1))) = k1_tops_1(X0,k4_xboole_0(u1_struct_0(X0),X1))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_2336])).

cnf(c_48153,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0)) ),
    inference(superposition,[status(thm)],[c_1138,c_14912])).

cnf(c_48362,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k2_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))))) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) ),
    inference(superposition,[status(thm)],[c_0,c_48153])).

cnf(c_51315,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))) ),
    inference(superposition,[status(thm)],[c_50939,c_48362])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_495,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_19])).

cnf(c_1147,plain,
    ( k1_tops_1(X0,X1) != X1
    | v3_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_496,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_19])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_19])).

cnf(c_788,plain,
    ( k1_tops_1(X1,X0) != X0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_496,c_494])).

cnf(c_789,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_788])).

cnf(c_790,plain,
    ( k1_tops_1(X0,X1) != X1
    | v3_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_5102,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_pre_topc(X1,X0) = iProver_top
    | k1_tops_1(X0,X1) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1147,c_790])).

cnf(c_5103,plain,
    ( k1_tops_1(X0,X1) != X1
    | v3_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5102])).

cnf(c_51690,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) != k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))
    | v3_pre_topc(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_51315,c_5103])).

cnf(c_54289,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) != k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))
    | v3_pre_topc(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51690,c_27,c_28])).

cnf(c_54302,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) != k1_tops_1(sK0,sK1)
    | v3_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6172,c_54289])).

cnf(c_7374,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_6172,c_0])).

cnf(c_3613,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1156,c_1134])).

cnf(c_6162,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5571,c_3613])).

cnf(c_34434,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k3_subset_1(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_7374,c_6162])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1157,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5570,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1157,c_1136])).

cnf(c_1582,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_1787,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_1156])).

cnf(c_2257,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1153])).

cnf(c_1158,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2696,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2257,c_1158])).

cnf(c_3330,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1787,c_2696])).

cnf(c_5606,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5570,c_3330])).

cnf(c_34513,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34434,c_5606])).

cnf(c_54379,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_xboole_0)
    | v3_pre_topc(k4_xboole_0(sK1,k1_xboole_0),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_54302,c_34513])).

cnf(c_54380,plain,
    ( k1_tops_1(sK0,sK1) != sK1
    | v3_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54379,c_5])).

cnf(c_55258,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_54380,c_29])).

cnf(c_55259,plain,
    ( k1_tops_1(sK0,sK1) != sK1
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_55258])).

cnf(c_55260,plain,
    ( v3_pre_topc(sK1,sK0)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_55259])).

cnf(c_6173,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_5571,c_5725])).

cnf(c_80949,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_78920,c_6173])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1149,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8992,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1149])).

cnf(c_1483,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_9314,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8992,c_25,c_24,c_1483])).

cnf(c_78921,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_65542,c_9314])).

cnf(c_80479,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_78921,c_1776])).

cnf(c_87068,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_80949,c_80479])).

cnf(c_87222,plain,
    ( v3_pre_topc(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_86280,c_1559,c_43181,c_55260,c_87068])).

cnf(c_87289,plain,
    ( k1_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_80950,c_1559,c_43181,c_87068])).

cnf(c_87317,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_87289,c_9314])).

cnf(c_22,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_87317,c_87222,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:05:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.58/3.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.58/3.53  
% 23.58/3.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.58/3.53  
% 23.58/3.53  ------  iProver source info
% 23.58/3.53  
% 23.58/3.53  git: date: 2020-06-30 10:37:57 +0100
% 23.58/3.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.58/3.53  git: non_committed_changes: false
% 23.58/3.53  git: last_make_outside_of_git: false
% 23.58/3.53  
% 23.58/3.53  ------ 
% 23.58/3.53  ------ Parsing...
% 23.58/3.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.58/3.53  
% 23.58/3.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.58/3.53  
% 23.58/3.53  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.58/3.53  
% 23.58/3.53  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.58/3.53  ------ Proving...
% 23.58/3.53  ------ Problem Properties 
% 23.58/3.53  
% 23.58/3.53  
% 23.58/3.53  clauses                                 30
% 23.58/3.53  conjectures                             5
% 23.58/3.53  EPR                                     6
% 23.58/3.53  Horn                                    27
% 23.58/3.53  unary                                   8
% 23.58/3.53  binary                                  11
% 23.58/3.53  lits                                    70
% 23.58/3.53  lits eq                                 14
% 23.58/3.53  fd_pure                                 0
% 23.58/3.53  fd_pseudo                               0
% 23.58/3.53  fd_cond                                 0
% 23.58/3.53  fd_pseudo_cond                          1
% 23.58/3.53  AC symbols                              0
% 23.58/3.53  
% 23.58/3.53  ------ Input Options Time Limit: Unbounded
% 23.58/3.53  
% 23.58/3.53  
% 23.58/3.53  ------ 
% 23.58/3.53  Current options:
% 23.58/3.53  ------ 
% 23.58/3.53  
% 23.58/3.53  
% 23.58/3.53  
% 23.58/3.53  
% 23.58/3.53  ------ Proving...
% 23.58/3.53  
% 23.58/3.53  
% 23.58/3.53  % SZS status Theorem for theBenchmark.p
% 23.58/3.53  
% 23.58/3.53  % SZS output start CNFRefutation for theBenchmark.p
% 23.58/3.53  
% 23.58/3.53  fof(f21,conjecture,(
% 23.58/3.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f22,negated_conjecture,(
% 23.58/3.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 23.58/3.53    inference(negated_conjecture,[],[f21])).
% 23.58/3.53  
% 23.58/3.53  fof(f39,plain,(
% 23.58/3.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 23.58/3.53    inference(ennf_transformation,[],[f22])).
% 23.58/3.53  
% 23.58/3.53  fof(f40,plain,(
% 23.58/3.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.58/3.53    inference(flattening,[],[f39])).
% 23.58/3.53  
% 23.58/3.53  fof(f44,plain,(
% 23.58/3.53    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.58/3.53    inference(nnf_transformation,[],[f40])).
% 23.58/3.53  
% 23.58/3.53  fof(f45,plain,(
% 23.58/3.53    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.58/3.53    inference(flattening,[],[f44])).
% 23.58/3.53  
% 23.58/3.53  fof(f47,plain,(
% 23.58/3.53    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) != k2_tops_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) = k2_tops_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 23.58/3.53    introduced(choice_axiom,[])).
% 23.58/3.53  
% 23.58/3.53  fof(f46,plain,(
% 23.58/3.53    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) != k2_tops_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) = k2_tops_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 23.58/3.53    introduced(choice_axiom,[])).
% 23.58/3.53  
% 23.58/3.53  fof(f48,plain,(
% 23.58/3.53    ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 23.58/3.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).
% 23.58/3.53  
% 23.58/3.53  fof(f74,plain,(
% 23.58/3.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 23.58/3.53    inference(cnf_transformation,[],[f48])).
% 23.58/3.53  
% 23.58/3.53  fof(f15,axiom,(
% 23.58/3.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f30,plain,(
% 23.58/3.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 23.58/3.53    inference(ennf_transformation,[],[f15])).
% 23.58/3.53  
% 23.58/3.53  fof(f31,plain,(
% 23.58/3.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 23.58/3.53    inference(flattening,[],[f30])).
% 23.58/3.53  
% 23.58/3.53  fof(f65,plain,(
% 23.58/3.53    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f31])).
% 23.58/3.53  
% 23.58/3.53  fof(f13,axiom,(
% 23.58/3.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f43,plain,(
% 23.58/3.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.58/3.53    inference(nnf_transformation,[],[f13])).
% 23.58/3.53  
% 23.58/3.53  fof(f63,plain,(
% 23.58/3.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.58/3.53    inference(cnf_transformation,[],[f43])).
% 23.58/3.53  
% 23.58/3.53  fof(f8,axiom,(
% 23.58/3.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f26,plain,(
% 23.58/3.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.58/3.53    inference(ennf_transformation,[],[f8])).
% 23.58/3.53  
% 23.58/3.53  fof(f58,plain,(
% 23.58/3.53    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.58/3.53    inference(cnf_transformation,[],[f26])).
% 23.58/3.53  
% 23.58/3.53  fof(f64,plain,(
% 23.58/3.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f43])).
% 23.58/3.53  
% 23.58/3.53  fof(f6,axiom,(
% 23.58/3.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f24,plain,(
% 23.58/3.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.58/3.53    inference(ennf_transformation,[],[f6])).
% 23.58/3.53  
% 23.58/3.53  fof(f56,plain,(
% 23.58/3.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.58/3.53    inference(cnf_transformation,[],[f24])).
% 23.58/3.53  
% 23.58/3.53  fof(f73,plain,(
% 23.58/3.53    l1_pre_topc(sK0)),
% 23.58/3.53    inference(cnf_transformation,[],[f48])).
% 23.58/3.53  
% 23.58/3.53  fof(f3,axiom,(
% 23.58/3.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f53,plain,(
% 23.58/3.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f3])).
% 23.58/3.53  
% 23.58/3.53  fof(f9,axiom,(
% 23.58/3.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f27,plain,(
% 23.58/3.53    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.58/3.53    inference(ennf_transformation,[],[f9])).
% 23.58/3.53  
% 23.58/3.53  fof(f59,plain,(
% 23.58/3.53    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.58/3.53    inference(cnf_transformation,[],[f27])).
% 23.58/3.53  
% 23.58/3.53  fof(f75,plain,(
% 23.58/3.53    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 23.58/3.53    inference(cnf_transformation,[],[f48])).
% 23.58/3.53  
% 23.58/3.53  fof(f19,axiom,(
% 23.58/3.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f36,plain,(
% 23.58/3.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.58/3.53    inference(ennf_transformation,[],[f19])).
% 23.58/3.53  
% 23.58/3.53  fof(f37,plain,(
% 23.58/3.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.58/3.53    inference(flattening,[],[f36])).
% 23.58/3.53  
% 23.58/3.53  fof(f69,plain,(
% 23.58/3.53    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f37])).
% 23.58/3.53  
% 23.58/3.53  fof(f72,plain,(
% 23.58/3.53    v2_pre_topc(sK0)),
% 23.58/3.53    inference(cnf_transformation,[],[f48])).
% 23.58/3.53  
% 23.58/3.53  fof(f12,axiom,(
% 23.58/3.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f62,plain,(
% 23.58/3.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 23.58/3.53    inference(cnf_transformation,[],[f12])).
% 23.58/3.53  
% 23.58/3.53  fof(f16,axiom,(
% 23.58/3.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f32,plain,(
% 23.58/3.53    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.58/3.53    inference(ennf_transformation,[],[f16])).
% 23.58/3.53  
% 23.58/3.53  fof(f66,plain,(
% 23.58/3.53    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f32])).
% 23.58/3.53  
% 23.58/3.53  fof(f4,axiom,(
% 23.58/3.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f54,plain,(
% 23.58/3.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.58/3.53    inference(cnf_transformation,[],[f4])).
% 23.58/3.53  
% 23.58/3.53  fof(f2,axiom,(
% 23.58/3.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f41,plain,(
% 23.58/3.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.58/3.53    inference(nnf_transformation,[],[f2])).
% 23.58/3.53  
% 23.58/3.53  fof(f42,plain,(
% 23.58/3.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.58/3.53    inference(flattening,[],[f41])).
% 23.58/3.53  
% 23.58/3.53  fof(f52,plain,(
% 23.58/3.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f42])).
% 23.58/3.53  
% 23.58/3.53  fof(f20,axiom,(
% 23.58/3.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f38,plain,(
% 23.58/3.53    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.58/3.53    inference(ennf_transformation,[],[f20])).
% 23.58/3.53  
% 23.58/3.53  fof(f71,plain,(
% 23.58/3.53    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f38])).
% 23.58/3.53  
% 23.58/3.53  fof(f1,axiom,(
% 23.58/3.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f49,plain,(
% 23.58/3.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f1])).
% 23.58/3.53  
% 23.58/3.53  fof(f5,axiom,(
% 23.58/3.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f55,plain,(
% 23.58/3.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.58/3.53    inference(cnf_transformation,[],[f5])).
% 23.58/3.53  
% 23.58/3.53  fof(f77,plain,(
% 23.58/3.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 23.58/3.53    inference(definition_unfolding,[],[f49,f55,f55])).
% 23.58/3.53  
% 23.58/3.53  fof(f70,plain,(
% 23.58/3.53    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f37])).
% 23.58/3.53  
% 23.58/3.53  fof(f50,plain,(
% 23.58/3.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.58/3.53    inference(cnf_transformation,[],[f42])).
% 23.58/3.53  
% 23.58/3.53  fof(f80,plain,(
% 23.58/3.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.58/3.53    inference(equality_resolution,[],[f50])).
% 23.58/3.53  
% 23.58/3.53  fof(f18,axiom,(
% 23.58/3.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 23.58/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.58/3.53  
% 23.58/3.53  fof(f35,plain,(
% 23.58/3.53    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.58/3.53    inference(ennf_transformation,[],[f18])).
% 23.58/3.53  
% 23.58/3.53  fof(f68,plain,(
% 23.58/3.53    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.58/3.53    inference(cnf_transformation,[],[f35])).
% 23.58/3.53  
% 23.58/3.53  fof(f76,plain,(
% 23.58/3.53    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 23.58/3.53    inference(cnf_transformation,[],[f48])).
% 23.58/3.53  
% 23.58/3.53  cnf(c_24,negated_conjecture,
% 23.58/3.53      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.58/3.53      inference(cnf_transformation,[],[f74]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1139,plain,
% 23.58/3.53      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_15,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ l1_pre_topc(X1) ),
% 23.58/3.53      inference(cnf_transformation,[],[f65]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1152,plain,
% 23.58/3.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.58/3.53      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 23.58/3.53      | l1_pre_topc(X1) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_14,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.58/3.53      inference(cnf_transformation,[],[f63]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1153,plain,
% 23.58/3.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.58/3.53      | r1_tarski(X0,X1) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_6592,plain,
% 23.58/3.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.58/3.53      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
% 23.58/3.53      | l1_pre_topc(X1) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1152,c_1153]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_8,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.58/3.53      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 23.58/3.53      inference(cnf_transformation,[],[f58]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_13,plain,
% 23.58/3.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.58/3.53      inference(cnf_transformation,[],[f64]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_177,plain,
% 23.58/3.53      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 23.58/3.53      inference(prop_impl,[status(thm)],[c_13]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_178,plain,
% 23.58/3.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.58/3.53      inference(renaming,[status(thm)],[c_177]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_228,plain,
% 23.58/3.53      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 23.58/3.53      inference(bin_hyper_res,[status(thm)],[c_8,c_178]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1134,plain,
% 23.58/3.53      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 23.58/3.53      | r1_tarski(X1,X0) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_228]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_27642,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))) = k2_pre_topc(X0,X1)
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_6592,c_1134]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_64509,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1139,c_27642]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_6,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.58/3.53      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.58/3.53      inference(cnf_transformation,[],[f56]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_226,plain,
% 23.58/3.53      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.58/3.53      inference(bin_hyper_res,[status(thm)],[c_6,c_178]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1136,plain,
% 23.58/3.53      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 23.58/3.53      | r1_tarski(X1,X0) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_27641,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1)) = k4_xboole_0(u1_struct_0(X0),k2_pre_topc(X0,X1))
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_6592,c_1136]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_61331,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1139,c_27641]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_25,negated_conjecture,
% 23.58/3.53      ( l1_pre_topc(sK0) ),
% 23.58/3.53      inference(cnf_transformation,[],[f73]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_28,plain,
% 23.58/3.53      ( l1_pre_topc(sK0) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_62880,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_61331,c_28]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_64512,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(light_normalisation,[status(thm)],[c_64509,c_62880]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_4,plain,
% 23.58/3.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 23.58/3.53      inference(cnf_transformation,[],[f53]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1156,plain,
% 23.58/3.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5571,plain,
% 23.58/3.53      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1156,c_1136]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_64513,plain,
% 23.58/3.53      ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(demodulation,[status(thm)],[c_64512,c_5571]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_65268,plain,
% 23.58/3.53      ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_64513,c_28]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_9,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.58/3.53      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 23.58/3.53      inference(cnf_transformation,[],[f59]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_229,plain,
% 23.58/3.53      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 23.58/3.53      inference(bin_hyper_res,[status(thm)],[c_9,c_178]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1133,plain,
% 23.58/3.53      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 23.58/3.53      | r1_tarski(X1,X0) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_42906,plain,
% 23.58/3.53      ( k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1156,c_1133]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_65274,plain,
% 23.58/3.53      ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_65268,c_42906]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_65542,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 23.58/3.53      inference(light_normalisation,[status(thm)],[c_65274,c_65268]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_23,negated_conjecture,
% 23.58/3.53      ( v3_pre_topc(sK1,sK0)
% 23.58/3.53      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(cnf_transformation,[],[f75]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1140,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 23.58/3.53      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_2258,plain,
% 23.58/3.53      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1139,c_1153]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1154,plain,
% 23.58/3.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.58/3.53      | r1_tarski(X0,X1) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_20,plain,
% 23.58/3.53      ( ~ v3_pre_topc(X0,X1)
% 23.58/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 23.58/3.53      | ~ v2_pre_topc(X3)
% 23.58/3.53      | ~ l1_pre_topc(X3)
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | k1_tops_1(X1,X0) = X0 ),
% 23.58/3.53      inference(cnf_transformation,[],[f69]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_492,plain,
% 23.58/3.53      ( ~ v3_pre_topc(X0,X1)
% 23.58/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | k1_tops_1(X1,X0) = X0
% 23.58/3.53      | ~ sP1_iProver_split ),
% 23.58/3.53      inference(splitting,
% 23.58/3.53                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 23.58/3.53                [c_20]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1144,plain,
% 23.58/3.53      ( k1_tops_1(X0,X1) = X1
% 23.58/3.53      | v3_pre_topc(X1,X0) != iProver_top
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top
% 23.58/3.53      | sP1_iProver_split != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_2474,plain,
% 23.58/3.53      ( k1_tops_1(X0,X1) = X1
% 23.58/3.53      | v3_pre_topc(X1,X0) != iProver_top
% 23.58/3.53      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top
% 23.58/3.53      | sP1_iProver_split != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1154,c_1144]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_26,negated_conjecture,
% 23.58/3.53      ( v2_pre_topc(sK0) ),
% 23.58/3.53      inference(cnf_transformation,[],[f72]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_27,plain,
% 23.58/3.53      ( v2_pre_topc(sK0) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_493,plain,
% 23.58/3.53      ( sP1_iProver_split | sP0_iProver_split ),
% 23.58/3.53      inference(splitting,
% 23.58/3.53                [splitting(split),new_symbols(definition,[])],
% 23.58/3.53                [c_20]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_540,plain,
% 23.58/3.53      ( sP1_iProver_split = iProver_top
% 23.58/3.53      | sP0_iProver_split = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_12,plain,
% 23.58/3.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 23.58/3.53      inference(cnf_transformation,[],[f62]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1155,plain,
% 23.58/3.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_491,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ v2_pre_topc(X1)
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | ~ sP0_iProver_split ),
% 23.58/3.53      inference(splitting,
% 23.58/3.53                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 23.58/3.53                [c_20]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1145,plain,
% 23.58/3.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.58/3.53      | v2_pre_topc(X1) != iProver_top
% 23.58/3.53      | l1_pre_topc(X1) != iProver_top
% 23.58/3.53      | sP0_iProver_split != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_3962,plain,
% 23.58/3.53      ( v2_pre_topc(X0) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top
% 23.58/3.53      | sP0_iProver_split != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1155,c_1145]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_3983,plain,
% 23.58/3.53      ( v2_pre_topc(sK0) != iProver_top
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top
% 23.58/3.53      | sP0_iProver_split != iProver_top ),
% 23.58/3.53      inference(instantiation,[status(thm)],[c_3962]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_16774,plain,
% 23.58/3.53      ( l1_pre_topc(X0) != iProver_top
% 23.58/3.53      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 23.58/3.53      | v3_pre_topc(X1,X0) != iProver_top
% 23.58/3.53      | k1_tops_1(X0,X1) = X1 ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_2474,c_27,c_28,c_540,c_3983]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_16775,plain,
% 23.58/3.53      ( k1_tops_1(X0,X1) = X1
% 23.58/3.53      | v3_pre_topc(X1,X0) != iProver_top
% 23.58/3.53      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(renaming,[status(thm)],[c_16774]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_16787,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1
% 23.58/3.53      | v3_pre_topc(sK1,sK0) != iProver_top
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_2258,c_16775]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_2476,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1
% 23.58/3.53      | v3_pre_topc(sK1,sK0) != iProver_top
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top
% 23.58/3.53      | sP1_iProver_split != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1139,c_1144]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_18521,plain,
% 23.58/3.53      ( v3_pre_topc(sK1,sK0) != iProver_top | k1_tops_1(sK0,sK1) = sK1 ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_16787,c_27,c_28,c_540,c_2476,c_3983]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_18522,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1 | v3_pre_topc(sK1,sK0) != iProver_top ),
% 23.58/3.53      inference(renaming,[status(thm)],[c_18521]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_18527,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 23.58/3.53      | k1_tops_1(sK0,sK1) = sK1 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1140,c_18522]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_78920,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1
% 23.58/3.53      | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_65542,c_18527]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_16,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 23.58/3.53      | ~ l1_pre_topc(X1) ),
% 23.58/3.53      inference(cnf_transformation,[],[f66]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1151,plain,
% 23.58/3.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.58/3.53      | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 23.58/3.53      | l1_pre_topc(X1) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_4343,plain,
% 23.58/3.53      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1139,c_1151]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_29,plain,
% 23.58/3.53      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1411,plain,
% 23.58/3.53      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.58/3.53      | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 23.58/3.53      | ~ l1_pre_topc(sK0) ),
% 23.58/3.53      inference(instantiation,[status(thm)],[c_16]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1412,plain,
% 23.58/3.53      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.58/3.53      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_4362,plain,
% 23.58/3.53      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_4343,c_28,c_29,c_1412]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5574,plain,
% 23.58/3.53      ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_4362,c_1136]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_4367,plain,
% 23.58/3.53      ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_4362,c_1134]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5725,plain,
% 23.58/3.53      ( k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 23.58/3.53      inference(demodulation,[status(thm)],[c_5574,c_4367]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_80950,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1
% 23.58/3.53      | k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_78920,c_5725]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_2509,plain,
% 23.58/3.53      ( ~ v3_pre_topc(sK1,sK0)
% 23.58/3.53      | ~ l1_pre_topc(sK0)
% 23.58/3.53      | ~ sP1_iProver_split
% 23.58/3.53      | k1_tops_1(sK0,sK1) = sK1 ),
% 23.58/3.53      inference(predicate_to_equality_rev,[status(thm)],[c_2476]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_3982,plain,
% 23.58/3.53      ( ~ v2_pre_topc(X0) | ~ l1_pre_topc(X0) | ~ sP0_iProver_split ),
% 23.58/3.53      inference(predicate_to_equality_rev,[status(thm)],[c_3962]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_3984,plain,
% 23.58/3.53      ( ~ v2_pre_topc(sK0) | ~ l1_pre_topc(sK0) | ~ sP0_iProver_split ),
% 23.58/3.53      inference(instantiation,[status(thm)],[c_3982]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_504,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.58/3.53      theory(equality) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_498,plain,( X0 = X0 ),theory(equality) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_4478,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 23.58/3.53      inference(resolution,[status(thm)],[c_504,c_498]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_499,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5,plain,
% 23.58/3.53      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.58/3.53      inference(cnf_transformation,[],[f54]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_2821,plain,
% 23.58/3.53      ( X0 != X1 | k4_xboole_0(X1,k1_xboole_0) = X0 ),
% 23.58/3.53      inference(resolution,[status(thm)],[c_499,c_5]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_10284,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,X1)
% 23.58/3.53      | m1_subset_1(k4_xboole_0(X2,k1_xboole_0),X1)
% 23.58/3.53      | X0 != X2 ),
% 23.58/3.53      inference(resolution,[status(thm)],[c_4478,c_2821]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_84514,plain,
% 23.58/3.53      ( v3_pre_topc(sK1,sK0)
% 23.58/3.53      | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1),X0)
% 23.58/3.53      | m1_subset_1(k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0),X0) ),
% 23.58/3.53      inference(resolution,[status(thm)],[c_10284,c_23]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_4458,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,X1)
% 23.58/3.53      | m1_subset_1(X2,k4_xboole_0(X1,k1_xboole_0))
% 23.58/3.53      | X2 != X0 ),
% 23.58/3.53      inference(resolution,[status(thm)],[c_504,c_5]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_16551,plain,
% 23.58/3.53      ( v3_pre_topc(sK1,sK0)
% 23.58/3.53      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1),k4_xboole_0(X0,k1_xboole_0))
% 23.58/3.53      | ~ m1_subset_1(k2_tops_1(sK0,sK1),X0) ),
% 23.58/3.53      inference(resolution,[status(thm)],[c_4458,c_23]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_86280,plain,
% 23.58/3.53      ( v3_pre_topc(sK1,sK0)
% 23.58/3.53      | ~ m1_subset_1(k2_tops_1(sK0,sK1),X0)
% 23.58/3.53      | m1_subset_1(k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) ),
% 23.58/3.53      inference(resolution,[status(thm)],[c_84514,c_16551]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1,plain,
% 23.58/3.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.58/3.53      inference(cnf_transformation,[],[f52]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1558,plain,
% 23.58/3.53      ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 23.58/3.53      | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
% 23.58/3.53      | k1_tops_1(sK0,sK1) = sK1 ),
% 23.58/3.53      inference(instantiation,[status(thm)],[c_1]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1559,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1
% 23.58/3.53      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 23.58/3.53      | r1_tarski(sK1,k1_tops_1(sK0,sK1)) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_21,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 23.58/3.53      inference(cnf_transformation,[],[f71]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1142,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1568,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1139,c_1142]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1471,plain,
% 23.58/3.53      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.58/3.53      | ~ l1_pre_topc(sK0)
% 23.58/3.53      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(instantiation,[status(thm)],[c_21]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1944,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_1568,c_25,c_24,c_1471]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_42910,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_2258,c_1133]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_43165,plain,
% 23.58/3.53      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1944,c_42910]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_43181,plain,
% 23.58/3.53      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_43165,c_1156]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5573,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_2258,c_1136]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_3615,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_2258,c_1134]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5723,plain,
% 23.58/3.53      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 23.58/3.53      inference(demodulation,[status(thm)],[c_5573,c_3615]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_6172,plain,
% 23.58/3.53      ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_5571,c_5723]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1138,plain,
% 23.58/3.53      ( l1_pre_topc(sK0) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_0,plain,
% 23.58/3.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.58/3.53      inference(cnf_transformation,[],[f77]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1776,plain,
% 23.58/3.53      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_0,c_1156]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_2336,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 23.58/3.53      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1154,c_1142]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_14915,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(X0),k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))),k2_tops_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))))) = k1_tops_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))))
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1776,c_2336]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_50939,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k2_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))))) = k1_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1138,c_14915]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_14912,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1),k2_tops_1(X0,k4_xboole_0(u1_struct_0(X0),X1))) = k1_tops_1(X0,k4_xboole_0(u1_struct_0(X0),X1))
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1156,c_2336]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_48153,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0)) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1138,c_14912]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_48362,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k2_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))))) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_0,c_48153]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_51315,plain,
% 23.58/3.53      ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_50939,c_48362]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_19,plain,
% 23.58/3.53      ( v3_pre_topc(X0,X1)
% 23.58/3.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 23.58/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ v2_pre_topc(X1)
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | ~ l1_pre_topc(X3)
% 23.58/3.53      | k1_tops_1(X1,X0) != X0 ),
% 23.58/3.53      inference(cnf_transformation,[],[f70]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_495,plain,
% 23.58/3.53      ( v3_pre_topc(X0,X1)
% 23.58/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ v2_pre_topc(X1)
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | k1_tops_1(X1,X0) != X0
% 23.58/3.53      | ~ sP3_iProver_split ),
% 23.58/3.53      inference(splitting,
% 23.58/3.53                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 23.58/3.53                [c_19]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1147,plain,
% 23.58/3.53      ( k1_tops_1(X0,X1) != X1
% 23.58/3.53      | v3_pre_topc(X1,X0) = iProver_top
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | v2_pre_topc(X0) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top
% 23.58/3.53      | sP3_iProver_split != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_496,plain,
% 23.58/3.53      ( sP3_iProver_split | sP2_iProver_split ),
% 23.58/3.53      inference(splitting,
% 23.58/3.53                [splitting(split),new_symbols(definition,[])],
% 23.58/3.53                [c_19]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_494,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | ~ sP2_iProver_split ),
% 23.58/3.53      inference(splitting,
% 23.58/3.53                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 23.58/3.53                [c_19]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_788,plain,
% 23.58/3.53      ( k1_tops_1(X1,X0) != X0
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | ~ v2_pre_topc(X1)
% 23.58/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | v3_pre_topc(X0,X1) ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_495,c_496,c_494]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_789,plain,
% 23.58/3.53      ( v3_pre_topc(X0,X1)
% 23.58/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ v2_pre_topc(X1)
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | k1_tops_1(X1,X0) != X0 ),
% 23.58/3.53      inference(renaming,[status(thm)],[c_788]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_790,plain,
% 23.58/3.53      ( k1_tops_1(X0,X1) != X1
% 23.58/3.53      | v3_pre_topc(X1,X0) = iProver_top
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | v2_pre_topc(X0) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5102,plain,
% 23.58/3.53      ( l1_pre_topc(X0) != iProver_top
% 23.58/3.53      | v2_pre_topc(X0) != iProver_top
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | v3_pre_topc(X1,X0) = iProver_top
% 23.58/3.53      | k1_tops_1(X0,X1) != X1 ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_1147,c_790]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5103,plain,
% 23.58/3.53      ( k1_tops_1(X0,X1) != X1
% 23.58/3.53      | v3_pre_topc(X1,X0) = iProver_top
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | v2_pre_topc(X0) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(renaming,[status(thm)],[c_5102]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_51690,plain,
% 23.58/3.53      ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) != k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))
% 23.58/3.53      | v3_pre_topc(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),sK0) = iProver_top
% 23.58/3.53      | m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.58/3.53      | v2_pre_topc(sK0) != iProver_top
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_51315,c_5103]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_54289,plain,
% 23.58/3.53      ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) != k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))
% 23.58/3.53      | v3_pre_topc(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),sK0) = iProver_top
% 23.58/3.53      | m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_51690,c_27,c_28]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_54302,plain,
% 23.58/3.53      ( k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) != k1_tops_1(sK0,sK1)
% 23.58/3.53      | v3_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))),sK0) = iProver_top
% 23.58/3.53      | m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_6172,c_54289]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_7374,plain,
% 23.58/3.53      ( k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) = sK1 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_6172,c_0]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_3613,plain,
% 23.58/3.53      ( k3_subset_1(X0,k3_subset_1(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1156,c_1134]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_6162,plain,
% 23.58/3.53      ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 23.58/3.53      inference(demodulation,[status(thm)],[c_5571,c_3613]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_34434,plain,
% 23.58/3.53      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k3_subset_1(sK1,sK1) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_7374,c_6162]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_3,plain,
% 23.58/3.53      ( r1_tarski(X0,X0) ),
% 23.58/3.53      inference(cnf_transformation,[],[f80]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1157,plain,
% 23.58/3.53      ( r1_tarski(X0,X0) = iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5570,plain,
% 23.58/3.53      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1157,c_1136]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1582,plain,
% 23.58/3.53      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1787,plain,
% 23.58/3.53      ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1582,c_1156]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_2257,plain,
% 23.58/3.53      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1155,c_1153]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1158,plain,
% 23.58/3.53      ( X0 = X1
% 23.58/3.53      | r1_tarski(X0,X1) != iProver_top
% 23.58/3.53      | r1_tarski(X1,X0) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_2696,plain,
% 23.58/3.53      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_2257,c_1158]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_3330,plain,
% 23.58/3.53      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1787,c_2696]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_5606,plain,
% 23.58/3.53      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 23.58/3.53      inference(light_normalisation,[status(thm)],[c_5570,c_3330]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_34513,plain,
% 23.58/3.53      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 23.58/3.53      inference(demodulation,[status(thm)],[c_34434,c_5606]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_54379,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_xboole_0)
% 23.58/3.53      | v3_pre_topc(k4_xboole_0(sK1,k1_xboole_0),sK0) = iProver_top
% 23.58/3.53      | m1_subset_1(k4_xboole_0(sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.58/3.53      inference(light_normalisation,[status(thm)],[c_54302,c_34513]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_54380,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) != sK1
% 23.58/3.53      | v3_pre_topc(sK1,sK0) = iProver_top
% 23.58/3.53      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.58/3.53      inference(demodulation,[status(thm)],[c_54379,c_5]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_55258,plain,
% 23.58/3.53      ( v3_pre_topc(sK1,sK0) = iProver_top | k1_tops_1(sK0,sK1) != sK1 ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_54380,c_29]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_55259,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) != sK1 | v3_pre_topc(sK1,sK0) = iProver_top ),
% 23.58/3.53      inference(renaming,[status(thm)],[c_55258]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_55260,plain,
% 23.58/3.53      ( v3_pre_topc(sK1,sK0) | k1_tops_1(sK0,sK1) != sK1 ),
% 23.58/3.53      inference(predicate_to_equality_rev,[status(thm)],[c_55259]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_6173,plain,
% 23.58/3.53      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_5571,c_5725]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_80949,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1
% 23.58/3.53      | k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_78920,c_6173]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_18,plain,
% 23.58/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.58/3.53      | ~ l1_pre_topc(X1)
% 23.58/3.53      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 23.58/3.53      inference(cnf_transformation,[],[f68]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1149,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 23.58/3.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.58/3.53      | l1_pre_topc(X0) != iProver_top ),
% 23.58/3.53      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_8992,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 23.58/3.53      | l1_pre_topc(sK0) != iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_1139,c_1149]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_1483,plain,
% 23.58/3.53      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.58/3.53      | ~ l1_pre_topc(sK0)
% 23.58/3.53      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(instantiation,[status(thm)],[c_18]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_9314,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_8992,c_25,c_24,c_1483]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_78921,plain,
% 23.58/3.53      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_65542,c_9314]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_80479,plain,
% 23.58/3.53      ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_78921,c_1776]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_87068,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1
% 23.58/3.53      | r1_tarski(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
% 23.58/3.53      inference(superposition,[status(thm)],[c_80949,c_80479]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_87222,plain,
% 23.58/3.53      ( v3_pre_topc(sK1,sK0) ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_86280,c_1559,c_43181,c_55260,c_87068]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_87289,plain,
% 23.58/3.53      ( k1_tops_1(sK0,sK1) = sK1 ),
% 23.58/3.53      inference(global_propositional_subsumption,
% 23.58/3.53                [status(thm)],
% 23.58/3.53                [c_80950,c_1559,c_43181,c_87068]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_87317,plain,
% 23.58/3.53      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(demodulation,[status(thm)],[c_87289,c_9314]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(c_22,negated_conjecture,
% 23.58/3.53      ( ~ v3_pre_topc(sK1,sK0)
% 23.58/3.53      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 23.58/3.53      inference(cnf_transformation,[],[f76]) ).
% 23.58/3.53  
% 23.58/3.53  cnf(contradiction,plain,
% 23.58/3.53      ( $false ),
% 23.58/3.53      inference(minisat,[status(thm)],[c_87317,c_87222,c_22]) ).
% 23.58/3.53  
% 23.58/3.53  
% 23.58/3.53  % SZS output end CNFRefutation for theBenchmark.p
% 23.58/3.53  
% 23.58/3.53  ------                               Statistics
% 23.58/3.53  
% 23.58/3.53  ------ Selected
% 23.58/3.53  
% 23.58/3.53  total_time:                             2.639
% 23.58/3.53  
%------------------------------------------------------------------------------
