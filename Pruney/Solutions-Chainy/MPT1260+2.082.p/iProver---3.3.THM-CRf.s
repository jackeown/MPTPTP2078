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
% DateTime   : Thu Dec  3 12:14:25 EST 2020

% Result     : Theorem 16.09s
% Output     : CNFRefutation 16.09s
% Verified   : 
% Statistics : Number of formulae       :  170 (1628 expanded)
%              Number of clauses        :  110 ( 487 expanded)
%              Number of leaves         :   17 ( 341 expanded)
%              Depth                    :   29
%              Number of atoms          :  505 (7988 expanded)
%              Number of equality atoms :  195 (2241 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   3 average)
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

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

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
    inference(flattening,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3402,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_3396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3405,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3986,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3396,c_3405])).

cnf(c_4681,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_3402,c_3986])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_168,plain,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_360,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_361,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_365,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_19])).

cnf(c_366,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_400,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_366,c_19])).

cnf(c_401,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,X1) = X1
    | sK1 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_168,c_401])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_18])).

cnf(c_733,plain,
    ( sP0_iProver_split
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_530])).

cnf(c_3392,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_11,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_317,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_318,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_19])).

cnf(c_323,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X1) != X0
    | k1_tops_1(sK0,X0) = X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_323,c_401])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_568])).

cnf(c_3394,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_3639,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3402,c_3394])).

cnf(c_3645,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3639])).

cnf(c_3960,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3392,c_733,c_3645])).

cnf(c_3961,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_3960])).

cnf(c_4743,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4681,c_3961])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_296,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | X2 != X0
    | k2_pre_topc(X3,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(X1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_418,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(X1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_19])).

cnf(c_419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK0,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_3399,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK0,X0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3408,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3404,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4112,plain,
    ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X1)) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_3404])).

cnf(c_7941,plain,
    ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X1))) = k7_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X1))
    | m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3408,c_4112])).

cnf(c_46427,plain,
    ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0))) = k7_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_7941])).

cnf(c_47002,plain,
    ( k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_3402,c_46427])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3409,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3744,plain,
    ( k3_subset_1(k2_pre_topc(sK0,X0),X0) = k4_xboole_0(k2_pre_topc(sK0,X0),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_3409])).

cnf(c_4488,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_3402,c_3744])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3406,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3707,plain,
    ( k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_3406])).

cnf(c_3937,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3402,c_3707])).

cnf(c_4530,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4488,c_3937])).

cnf(c_47051,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_47002,c_4488,c_4530])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3403,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3407,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3688,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(superposition,[status(thm)],[c_3403,c_3407])).

cnf(c_3985,plain,
    ( k7_subset_1(k2_pre_topc(sK0,X0),X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_3405])).

cnf(c_4416,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_3402,c_3985])).

cnf(c_47052,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_47051,c_3688,c_4416])).

cnf(c_47102,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = sK1
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4743,c_47052])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_3398,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_3576,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3402,c_3398])).

cnf(c_3984,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_3402,c_3405])).

cnf(c_4189,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3576,c_3984])).

cnf(c_47106,plain,
    ( k1_tops_1(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_47102,c_4189,c_4416])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_166,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_335,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_336,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_340,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_19])).

cnf(c_341,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_466,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_341])).

cnf(c_467,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,X1) != X1
    | sK1 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_166,c_467])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_18])).

cnf(c_732,plain,
    ( sP0_iProver_split
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_551])).

cnf(c_3393,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_4512,plain,
    ( k1_tops_1(sK0,sK1) != sK1
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3393,c_732,c_3645])).

cnf(c_4513,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(renaming,[status(thm)],[c_4512])).

cnf(c_4727,plain,
    ( k1_tops_1(sK0,sK1) != sK1
    | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4681,c_4513])).

cnf(c_47157,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_47106,c_4727])).

cnf(c_47170,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_47157])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_3397,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_3613,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3402,c_3397])).

cnf(c_4744,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4681,c_3613])).

cnf(c_47158,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_47106,c_4744])).

cnf(c_47171,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_47170,c_47158])).

cnf(c_47172,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_47171])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:05:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 16.09/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.09/2.48  
% 16.09/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 16.09/2.48  
% 16.09/2.48  ------  iProver source info
% 16.09/2.48  
% 16.09/2.48  git: date: 2020-06-30 10:37:57 +0100
% 16.09/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 16.09/2.48  git: non_committed_changes: false
% 16.09/2.48  git: last_make_outside_of_git: false
% 16.09/2.48  
% 16.09/2.48  ------ 
% 16.09/2.48  ------ Parsing...
% 16.09/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 16.09/2.48  ------ Proving...
% 16.09/2.48  ------ Problem Properties 
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  clauses                                 21
% 16.09/2.48  conjectures                             1
% 16.09/2.48  EPR                                     1
% 16.09/2.48  Horn                                    19
% 16.09/2.48  unary                                   3
% 16.09/2.48  binary                                  13
% 16.09/2.48  lits                                    45
% 16.09/2.48  lits eq                                 14
% 16.09/2.48  fd_pure                                 0
% 16.09/2.48  fd_pseudo                               0
% 16.09/2.48  fd_cond                                 0
% 16.09/2.48  fd_pseudo_cond                          0
% 16.09/2.48  AC symbols                              0
% 16.09/2.48  
% 16.09/2.48  ------ Input Options Time Limit: Unbounded
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 16.09/2.48  Current options:
% 16.09/2.48  ------ 
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  ------ Proving...
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 16.09/2.48  
% 16.09/2.48  ------ Proving...
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 16.09/2.48  
% 16.09/2.48  ------ Proving...
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 14 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 16.09/2.48  
% 16.09/2.48  ------ Proving...
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 16.09/2.48  
% 16.09/2.48  ------ Proving...
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 16.09/2.48  
% 16.09/2.48  ------ Proving...
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 16.09/2.48  
% 16.09/2.48  ------ Proving...
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  % SZS status Theorem for theBenchmark.p
% 16.09/2.48  
% 16.09/2.48   Resolution empty clause
% 16.09/2.48  
% 16.09/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 16.09/2.48  
% 16.09/2.48  fof(f17,conjecture,(
% 16.09/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f18,negated_conjecture,(
% 16.09/2.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 16.09/2.48    inference(negated_conjecture,[],[f17])).
% 16.09/2.48  
% 16.09/2.48  fof(f37,plain,(
% 16.09/2.48    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f18])).
% 16.09/2.48  
% 16.09/2.48  fof(f38,plain,(
% 16.09/2.48    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 16.09/2.48    inference(flattening,[],[f37])).
% 16.09/2.48  
% 16.09/2.48  fof(f39,plain,(
% 16.09/2.48    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 16.09/2.48    inference(nnf_transformation,[],[f38])).
% 16.09/2.48  
% 16.09/2.48  fof(f40,plain,(
% 16.09/2.48    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 16.09/2.48    inference(flattening,[],[f39])).
% 16.09/2.48  
% 16.09/2.48  fof(f42,plain,(
% 16.09/2.48    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) != k2_tops_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) = k2_tops_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 16.09/2.48    introduced(choice_axiom,[])).
% 16.09/2.48  
% 16.09/2.48  fof(f41,plain,(
% 16.09/2.48    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) != k2_tops_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) = k2_tops_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 16.09/2.48    introduced(choice_axiom,[])).
% 16.09/2.48  
% 16.09/2.48  fof(f43,plain,(
% 16.09/2.48    ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 16.09/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 16.09/2.48  
% 16.09/2.48  fof(f62,plain,(
% 16.09/2.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 16.09/2.48    inference(cnf_transformation,[],[f43])).
% 16.09/2.48  
% 16.09/2.48  fof(f11,axiom,(
% 16.09/2.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f28,plain,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f11])).
% 16.09/2.48  
% 16.09/2.48  fof(f29,plain,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 16.09/2.48    inference(flattening,[],[f28])).
% 16.09/2.48  
% 16.09/2.48  fof(f53,plain,(
% 16.09/2.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 16.09/2.48    inference(cnf_transformation,[],[f29])).
% 16.09/2.48  
% 16.09/2.48  fof(f61,plain,(
% 16.09/2.48    l1_pre_topc(sK0)),
% 16.09/2.48    inference(cnf_transformation,[],[f43])).
% 16.09/2.48  
% 16.09/2.48  fof(f6,axiom,(
% 16.09/2.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f25,plain,(
% 16.09/2.48    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f6])).
% 16.09/2.48  
% 16.09/2.48  fof(f49,plain,(
% 16.09/2.48    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 16.09/2.48    inference(cnf_transformation,[],[f25])).
% 16.09/2.48  
% 16.09/2.48  fof(f63,plain,(
% 16.09/2.48    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 16.09/2.48    inference(cnf_transformation,[],[f43])).
% 16.09/2.48  
% 16.09/2.48  fof(f15,axiom,(
% 16.09/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f34,plain,(
% 16.09/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f15])).
% 16.09/2.48  
% 16.09/2.48  fof(f35,plain,(
% 16.09/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 16.09/2.48    inference(flattening,[],[f34])).
% 16.09/2.48  
% 16.09/2.48  fof(f57,plain,(
% 16.09/2.48    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 16.09/2.48    inference(cnf_transformation,[],[f35])).
% 16.09/2.48  
% 16.09/2.48  fof(f60,plain,(
% 16.09/2.48    v2_pre_topc(sK0)),
% 16.09/2.48    inference(cnf_transformation,[],[f43])).
% 16.09/2.48  
% 16.09/2.48  fof(f13,axiom,(
% 16.09/2.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f31,plain,(
% 16.09/2.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f13])).
% 16.09/2.48  
% 16.09/2.48  fof(f32,plain,(
% 16.09/2.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 16.09/2.48    inference(flattening,[],[f31])).
% 16.09/2.48  
% 16.09/2.48  fof(f55,plain,(
% 16.09/2.48    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 16.09/2.48    inference(cnf_transformation,[],[f32])).
% 16.09/2.48  
% 16.09/2.48  fof(f9,axiom,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f19,plain,(
% 16.09/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 16.09/2.48    inference(unused_predicate_definition_removal,[],[f9])).
% 16.09/2.48  
% 16.09/2.48  fof(f27,plain,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 16.09/2.48    inference(ennf_transformation,[],[f19])).
% 16.09/2.48  
% 16.09/2.48  fof(f52,plain,(
% 16.09/2.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 16.09/2.48    inference(cnf_transformation,[],[f27])).
% 16.09/2.48  
% 16.09/2.48  fof(f12,axiom,(
% 16.09/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f30,plain,(
% 16.09/2.48    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 16.09/2.48    inference(ennf_transformation,[],[f12])).
% 16.09/2.48  
% 16.09/2.48  fof(f54,plain,(
% 16.09/2.48    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 16.09/2.48    inference(cnf_transformation,[],[f30])).
% 16.09/2.48  
% 16.09/2.48  fof(f3,axiom,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f22,plain,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f3])).
% 16.09/2.48  
% 16.09/2.48  fof(f46,plain,(
% 16.09/2.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 16.09/2.48    inference(cnf_transformation,[],[f22])).
% 16.09/2.48  
% 16.09/2.48  fof(f7,axiom,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f26,plain,(
% 16.09/2.48    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f7])).
% 16.09/2.48  
% 16.09/2.48  fof(f50,plain,(
% 16.09/2.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 16.09/2.48    inference(cnf_transformation,[],[f26])).
% 16.09/2.48  
% 16.09/2.48  fof(f2,axiom,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f21,plain,(
% 16.09/2.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f2])).
% 16.09/2.48  
% 16.09/2.48  fof(f45,plain,(
% 16.09/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 16.09/2.48    inference(cnf_transformation,[],[f21])).
% 16.09/2.48  
% 16.09/2.48  fof(f5,axiom,(
% 16.09/2.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f24,plain,(
% 16.09/2.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f5])).
% 16.09/2.48  
% 16.09/2.48  fof(f48,plain,(
% 16.09/2.48    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 16.09/2.48    inference(cnf_transformation,[],[f24])).
% 16.09/2.48  
% 16.09/2.48  fof(f8,axiom,(
% 16.09/2.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f51,plain,(
% 16.09/2.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 16.09/2.48    inference(cnf_transformation,[],[f8])).
% 16.09/2.48  
% 16.09/2.48  fof(f4,axiom,(
% 16.09/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f23,plain,(
% 16.09/2.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 16.09/2.48    inference(ennf_transformation,[],[f4])).
% 16.09/2.48  
% 16.09/2.48  fof(f47,plain,(
% 16.09/2.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 16.09/2.48    inference(cnf_transformation,[],[f23])).
% 16.09/2.48  
% 16.09/2.48  fof(f16,axiom,(
% 16.09/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f36,plain,(
% 16.09/2.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 16.09/2.48    inference(ennf_transformation,[],[f16])).
% 16.09/2.48  
% 16.09/2.48  fof(f59,plain,(
% 16.09/2.48    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 16.09/2.48    inference(cnf_transformation,[],[f36])).
% 16.09/2.48  
% 16.09/2.48  fof(f64,plain,(
% 16.09/2.48    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 16.09/2.48    inference(cnf_transformation,[],[f43])).
% 16.09/2.48  
% 16.09/2.48  fof(f58,plain,(
% 16.09/2.48    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 16.09/2.48    inference(cnf_transformation,[],[f35])).
% 16.09/2.48  
% 16.09/2.48  fof(f14,axiom,(
% 16.09/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 16.09/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.48  
% 16.09/2.48  fof(f33,plain,(
% 16.09/2.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 16.09/2.48    inference(ennf_transformation,[],[f14])).
% 16.09/2.48  
% 16.09/2.48  fof(f56,plain,(
% 16.09/2.48    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 16.09/2.48    inference(cnf_transformation,[],[f33])).
% 16.09/2.48  
% 16.09/2.48  cnf(c_18,negated_conjecture,
% 16.09/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 16.09/2.48      inference(cnf_transformation,[],[f62]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3402,plain,
% 16.09/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_9,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ l1_pre_topc(X1) ),
% 16.09/2.48      inference(cnf_transformation,[],[f53]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_19,negated_conjecture,
% 16.09/2.48      ( l1_pre_topc(sK0) ),
% 16.09/2.48      inference(cnf_transformation,[],[f61]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_454,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | sK0 != X1 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_455,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_454]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3396,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 16.09/2.48      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_5,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 16.09/2.48      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 16.09/2.48      inference(cnf_transformation,[],[f49]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3405,plain,
% 16.09/2.48      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 16.09/2.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3986,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3396,c_3405]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4681,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_3986]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_17,negated_conjecture,
% 16.09/2.48      ( v3_pre_topc(sK1,sK0)
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(cnf_transformation,[],[f63]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_168,plain,
% 16.09/2.48      ( v3_pre_topc(sK1,sK0)
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(prop_impl,[status(thm)],[c_17]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_14,plain,
% 16.09/2.48      ( ~ v3_pre_topc(X0,X1)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 16.09/2.48      | ~ v2_pre_topc(X3)
% 16.09/2.48      | ~ l1_pre_topc(X3)
% 16.09/2.48      | ~ l1_pre_topc(X1)
% 16.09/2.48      | k1_tops_1(X1,X0) = X0 ),
% 16.09/2.48      inference(cnf_transformation,[],[f57]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_20,negated_conjecture,
% 16.09/2.48      ( v2_pre_topc(sK0) ),
% 16.09/2.48      inference(cnf_transformation,[],[f60]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_360,plain,
% 16.09/2.48      ( ~ v3_pre_topc(X0,X1)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 16.09/2.48      | ~ l1_pre_topc(X1)
% 16.09/2.48      | ~ l1_pre_topc(X3)
% 16.09/2.48      | k1_tops_1(X1,X0) = X0
% 16.09/2.48      | sK0 != X3 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_361,plain,
% 16.09/2.48      ( ~ v3_pre_topc(X0,X1)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ l1_pre_topc(X1)
% 16.09/2.48      | ~ l1_pre_topc(sK0)
% 16.09/2.48      | k1_tops_1(X1,X0) = X0 ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_360]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_365,plain,
% 16.09/2.48      ( ~ l1_pre_topc(X1)
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ v3_pre_topc(X0,X1)
% 16.09/2.48      | k1_tops_1(X1,X0) = X0 ),
% 16.09/2.48      inference(global_propositional_subsumption,[status(thm)],[c_361,c_19]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_366,plain,
% 16.09/2.48      ( ~ v3_pre_topc(X0,X1)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ l1_pre_topc(X1)
% 16.09/2.48      | k1_tops_1(X1,X0) = X0 ),
% 16.09/2.48      inference(renaming,[status(thm)],[c_365]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_400,plain,
% 16.09/2.48      ( ~ v3_pre_topc(X0,X1)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k1_tops_1(X1,X0) = X0
% 16.09/2.48      | sK0 != X1 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_366,c_19]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_401,plain,
% 16.09/2.48      ( ~ v3_pre_topc(X0,sK0)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k1_tops_1(sK0,X0) = X0 ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_400]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_525,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,X1) = X1
% 16.09/2.48      | sK1 != X1
% 16.09/2.48      | sK0 != sK0 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_168,c_401]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_526,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) = sK1 ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_525]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_530,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) = sK1 ),
% 16.09/2.48      inference(global_propositional_subsumption,[status(thm)],[c_526,c_18]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_733,plain,
% 16.09/2.48      ( sP0_iProver_split
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) = sK1 ),
% 16.09/2.48      inference(splitting,
% 16.09/2.48                [splitting(split),new_symbols(definition,[])],
% 16.09/2.48                [c_530]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3392,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) = sK1
% 16.09/2.48      | sP0_iProver_split = iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_11,plain,
% 16.09/2.48      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 16.09/2.48      | ~ v2_pre_topc(X0)
% 16.09/2.48      | ~ l1_pre_topc(X0) ),
% 16.09/2.48      inference(cnf_transformation,[],[f55]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_317,plain,
% 16.09/2.48      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 16.09/2.48      | ~ l1_pre_topc(X0)
% 16.09/2.48      | sK0 != X0 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_318,plain,
% 16.09/2.48      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ l1_pre_topc(sK0) ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_317]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_322,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 16.09/2.48      inference(global_propositional_subsumption,[status(thm)],[c_318,c_19]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_323,plain,
% 16.09/2.48      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 16.09/2.48      inference(renaming,[status(thm)],[c_322]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_567,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k1_tops_1(sK0,X1) != X0
% 16.09/2.48      | k1_tops_1(sK0,X0) = X0
% 16.09/2.48      | sK0 != sK0 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_323,c_401]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_568,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_567]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_729,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~ sP0_iProver_split ),
% 16.09/2.48      inference(splitting,
% 16.09/2.48                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 16.09/2.48                [c_568]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3394,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 16.09/2.48      | sP0_iProver_split != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3639,plain,
% 16.09/2.48      ( sP0_iProver_split != iProver_top ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_3394]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3645,plain,
% 16.09/2.48      ( ~ sP0_iProver_split ),
% 16.09/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_3639]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3960,plain,
% 16.09/2.48      ( k1_tops_1(sK0,sK1) = sK1
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(global_propositional_subsumption,
% 16.09/2.48                [status(thm)],
% 16.09/2.48                [c_3392,c_733,c_3645]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3961,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) = sK1 ),
% 16.09/2.48      inference(renaming,[status(thm)],[c_3960]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4743,plain,
% 16.09/2.48      ( k1_tops_1(sK0,sK1) = sK1
% 16.09/2.48      | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_4681,c_3961]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_8,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 16.09/2.48      inference(cnf_transformation,[],[f52]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_10,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 16.09/2.48      | ~ l1_pre_topc(X1) ),
% 16.09/2.48      inference(cnf_transformation,[],[f54]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_296,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 16.09/2.48      | ~ l1_pre_topc(X3)
% 16.09/2.48      | X2 != X0
% 16.09/2.48      | k2_pre_topc(X3,X2) != X1 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_297,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(X1,X0)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ l1_pre_topc(X1) ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_296]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_418,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(X1,X0)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | sK0 != X1 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_297,c_19]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_419,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK0,X0)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_418]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3399,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK0,X0))) = iProver_top
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_2,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 16.09/2.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 16.09/2.48      inference(cnf_transformation,[],[f46]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3408,plain,
% 16.09/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 16.09/2.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_6,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 16.09/2.48      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 16.09/2.48      inference(cnf_transformation,[],[f50]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3404,plain,
% 16.09/2.48      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 16.09/2.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 16.09/2.48      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4112,plain,
% 16.09/2.48      ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X1)) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1)
% 16.09/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,X0))) != iProver_top
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3399,c_3404]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_7941,plain,
% 16.09/2.48      ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X1))) = k7_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X1))
% 16.09/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,X0))) != iProver_top
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3408,c_4112]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_46427,plain,
% 16.09/2.48      ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0))) = k7_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X0))
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3399,c_7941]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47002,plain,
% 16.09/2.48      ( k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_46427]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_1,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 16.09/2.48      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 16.09/2.48      inference(cnf_transformation,[],[f45]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3409,plain,
% 16.09/2.48      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 16.09/2.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3744,plain,
% 16.09/2.48      ( k3_subset_1(k2_pre_topc(sK0,X0),X0) = k4_xboole_0(k2_pre_topc(sK0,X0),X0)
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3399,c_3409]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4488,plain,
% 16.09/2.48      ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_3744]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 16.09/2.48      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 16.09/2.48      inference(cnf_transformation,[],[f48]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3406,plain,
% 16.09/2.48      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 16.09/2.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3707,plain,
% 16.09/2.48      ( k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0)) = X0
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3399,c_3406]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3937,plain,
% 16.09/2.48      ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_3707]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4530,plain,
% 16.09/2.48      ( k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 16.09/2.48      inference(demodulation,[status(thm)],[c_4488,c_3937]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47051,plain,
% 16.09/2.48      ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) ),
% 16.09/2.48      inference(light_normalisation,[status(thm)],[c_47002,c_4488,c_4530]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_7,plain,
% 16.09/2.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 16.09/2.48      inference(cnf_transformation,[],[f51]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3403,plain,
% 16.09/2.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 16.09/2.48      inference(cnf_transformation,[],[f47]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3407,plain,
% 16.09/2.48      ( k9_subset_1(X0,X1,X1) = X1
% 16.09/2.48      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3688,plain,
% 16.09/2.48      ( k9_subset_1(X0,X1,X1) = X1 ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3403,c_3407]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3985,plain,
% 16.09/2.48      ( k7_subset_1(k2_pre_topc(sK0,X0),X0,X1) = k4_xboole_0(X0,X1)
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3399,c_3405]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4416,plain,
% 16.09/2.48      ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_3985]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47052,plain,
% 16.09/2.48      ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 16.09/2.48      inference(demodulation,[status(thm)],[c_47051,c_3688,c_4416]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47102,plain,
% 16.09/2.48      ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = sK1
% 16.09/2.48      | k1_tops_1(sK0,sK1) = sK1 ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_4743,c_47052]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_15,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ l1_pre_topc(X1)
% 16.09/2.48      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 16.09/2.48      inference(cnf_transformation,[],[f59]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_430,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 16.09/2.48      | sK0 != X1 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_431,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_430]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3398,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3576,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_3398]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3984,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_3405]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4189,plain,
% 16.09/2.48      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3576,c_3984]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47106,plain,
% 16.09/2.48      ( k1_tops_1(sK0,sK1) = sK1 ),
% 16.09/2.48      inference(demodulation,[status(thm)],[c_47102,c_4189,c_4416]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_16,negated_conjecture,
% 16.09/2.48      ( ~ v3_pre_topc(sK1,sK0)
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(cnf_transformation,[],[f64]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_166,plain,
% 16.09/2.48      ( ~ v3_pre_topc(sK1,sK0)
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(prop_impl,[status(thm)],[c_16]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_13,plain,
% 16.09/2.48      ( v3_pre_topc(X0,X1)
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ v2_pre_topc(X1)
% 16.09/2.48      | ~ l1_pre_topc(X1)
% 16.09/2.48      | ~ l1_pre_topc(X3)
% 16.09/2.48      | k1_tops_1(X1,X0) != X0 ),
% 16.09/2.48      inference(cnf_transformation,[],[f58]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_335,plain,
% 16.09/2.48      ( v3_pre_topc(X0,X1)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 16.09/2.48      | ~ l1_pre_topc(X1)
% 16.09/2.48      | ~ l1_pre_topc(X3)
% 16.09/2.48      | k1_tops_1(X1,X0) != X0
% 16.09/2.48      | sK0 != X1 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_336,plain,
% 16.09/2.48      ( v3_pre_topc(X0,sK0)
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ l1_pre_topc(X2)
% 16.09/2.48      | ~ l1_pre_topc(sK0)
% 16.09/2.48      | k1_tops_1(sK0,X0) != X0 ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_335]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_340,plain,
% 16.09/2.48      ( ~ l1_pre_topc(X2)
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 16.09/2.48      | v3_pre_topc(X0,sK0)
% 16.09/2.48      | k1_tops_1(sK0,X0) != X0 ),
% 16.09/2.48      inference(global_propositional_subsumption,[status(thm)],[c_336,c_19]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_341,plain,
% 16.09/2.48      ( v3_pre_topc(X0,sK0)
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ l1_pre_topc(X2)
% 16.09/2.48      | k1_tops_1(sK0,X0) != X0 ),
% 16.09/2.48      inference(renaming,[status(thm)],[c_340]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_466,plain,
% 16.09/2.48      ( v3_pre_topc(X0,sK0)
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k1_tops_1(sK0,X0) != X0
% 16.09/2.48      | sK0 != X2 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_19,c_341]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_467,plain,
% 16.09/2.48      ( v3_pre_topc(X0,sK0)
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k1_tops_1(sK0,X0) != X0 ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_466]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_546,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,X1) != X1
% 16.09/2.48      | sK1 != X1
% 16.09/2.48      | sK0 != sK0 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_166,c_467]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_547,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) != sK1 ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_546]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_551,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) != sK1 ),
% 16.09/2.48      inference(global_propositional_subsumption,[status(thm)],[c_547,c_18]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_732,plain,
% 16.09/2.48      ( sP0_iProver_split
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) != sK1 ),
% 16.09/2.48      inference(splitting,
% 16.09/2.48                [splitting(split),new_symbols(definition,[])],
% 16.09/2.48                [c_551]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3393,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) != sK1
% 16.09/2.48      | sP0_iProver_split = iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4512,plain,
% 16.09/2.48      ( k1_tops_1(sK0,sK1) != sK1
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(global_propositional_subsumption,
% 16.09/2.48                [status(thm)],
% 16.09/2.48                [c_3393,c_732,c_3645]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4513,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 16.09/2.48      | k1_tops_1(sK0,sK1) != sK1 ),
% 16.09/2.48      inference(renaming,[status(thm)],[c_4512]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4727,plain,
% 16.09/2.48      ( k1_tops_1(sK0,sK1) != sK1
% 16.09/2.48      | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(demodulation,[status(thm)],[c_4681,c_4513]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47157,plain,
% 16.09/2.48      ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 16.09/2.48      | sK1 != sK1 ),
% 16.09/2.48      inference(demodulation,[status(thm)],[c_47106,c_4727]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47170,plain,
% 16.09/2.48      ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(equality_resolution_simp,[status(thm)],[c_47157]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_12,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | ~ l1_pre_topc(X1)
% 16.09/2.48      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 16.09/2.48      inference(cnf_transformation,[],[f56]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_442,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 16.09/2.48      | sK0 != X1 ),
% 16.09/2.48      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_443,plain,
% 16.09/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 16.09/2.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 16.09/2.48      inference(unflattening,[status(thm)],[c_442]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3397,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 16.09/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 16.09/2.48      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_3613,plain,
% 16.09/2.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_3402,c_3397]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_4744,plain,
% 16.09/2.48      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(superposition,[status(thm)],[c_4681,c_3613]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47158,plain,
% 16.09/2.48      ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(demodulation,[status(thm)],[c_47106,c_4744]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47171,plain,
% 16.09/2.48      ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 16.09/2.48      inference(light_normalisation,[status(thm)],[c_47170,c_47158]) ).
% 16.09/2.48  
% 16.09/2.48  cnf(c_47172,plain,
% 16.09/2.48      ( $false ),
% 16.09/2.48      inference(equality_resolution_simp,[status(thm)],[c_47171]) ).
% 16.09/2.48  
% 16.09/2.48  
% 16.09/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 16.09/2.48  
% 16.09/2.48  ------                               Statistics
% 16.09/2.48  
% 16.09/2.48  ------ Selected
% 16.09/2.48  
% 16.09/2.48  total_time:                             1.951
% 16.09/2.48  
%------------------------------------------------------------------------------
