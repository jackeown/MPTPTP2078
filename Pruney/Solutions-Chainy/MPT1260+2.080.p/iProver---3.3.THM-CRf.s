%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:25 EST 2020

% Result     : Theorem 19.30s
% Output     : CNFRefutation 19.30s
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
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

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
    inference(flattening,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f32])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

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

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

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

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

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

cnf(c_1058,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_1065,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

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

cnf(c_1055,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_1373,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_1055])).

cnf(c_1375,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1373])).

cnf(c_3832,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1058,c_733,c_1375])).

cnf(c_3833,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_3832])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_1060,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1067,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2306,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_1067])).

cnf(c_3819,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_1065,c_2306])).

cnf(c_3834,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3833,c_3819])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

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

cnf(c_1063,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK0,X0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1070,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1066,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2432,plain,
    ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X1)) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1066])).

cnf(c_9754,plain,
    ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X1))) = k7_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X1))
    | m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1070,c_2432])).

cnf(c_69160,plain,
    ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0))) = k7_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_9754])).

cnf(c_69372,plain,
    ( k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_1065,c_69160])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1072,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1603,plain,
    ( k3_subset_1(k2_pre_topc(sK0,X0),X0) = k4_xboole_0(k2_pre_topc(sK0,X0),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1072])).

cnf(c_2180,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_1065,c_1603])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1068,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1522,plain,
    ( k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1068])).

cnf(c_1895,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1065,c_1522])).

cnf(c_2556,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2180,c_1895])).

cnf(c_69398,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_69372,c_2180,c_2556])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1071,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1069,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1513,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(superposition,[status(thm)],[c_1071,c_1069])).

cnf(c_2305,plain,
    ( k7_subset_1(k2_pre_topc(sK0,X0),X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1067])).

cnf(c_2737,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1065,c_2305])).

cnf(c_69399,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_69398,c_1513,c_2737])).

cnf(c_69411,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = sK1
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3834,c_69399])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1062,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_1251,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1065,c_1062])).

cnf(c_2304,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1065,c_1067])).

cnf(c_2554,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1251,c_2304])).

cnf(c_69413,plain,
    ( k1_tops_1(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_69411,c_2554,c_2737])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

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
    inference(cnf_transformation,[],[f56])).

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

cnf(c_1056,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_3046,plain,
    ( k1_tops_1(sK0,sK1) != sK1
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1056,c_732,c_1375])).

cnf(c_3047,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(renaming,[status(thm)],[c_3046])).

cnf(c_3920,plain,
    ( k1_tops_1(sK0,sK1) != sK1
    | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3819,c_3047])).

cnf(c_69542,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_69413,c_3920])).

cnf(c_69547,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_69542])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_1061,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_1320,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1065,c_1061])).

cnf(c_3925,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1320,c_3819])).

cnf(c_69543,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_69413,c_3925])).

cnf(c_69548,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_69547,c_69543])).

cnf(c_69549,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_69548])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:38:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.30/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.30/2.98  
% 19.30/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.30/2.98  
% 19.30/2.98  ------  iProver source info
% 19.30/2.98  
% 19.30/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.30/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.30/2.98  git: non_committed_changes: false
% 19.30/2.98  git: last_make_outside_of_git: false
% 19.30/2.98  
% 19.30/2.98  ------ 
% 19.30/2.98  
% 19.30/2.98  ------ Input Options
% 19.30/2.98  
% 19.30/2.98  --out_options                           all
% 19.30/2.98  --tptp_safe_out                         true
% 19.30/2.98  --problem_path                          ""
% 19.30/2.98  --include_path                          ""
% 19.30/2.98  --clausifier                            res/vclausify_rel
% 19.30/2.98  --clausifier_options                    ""
% 19.30/2.98  --stdin                                 false
% 19.30/2.98  --stats_out                             all
% 19.30/2.98  
% 19.30/2.98  ------ General Options
% 19.30/2.98  
% 19.30/2.98  --fof                                   false
% 19.30/2.98  --time_out_real                         305.
% 19.30/2.98  --time_out_virtual                      -1.
% 19.30/2.98  --symbol_type_check                     false
% 19.30/2.98  --clausify_out                          false
% 19.30/2.98  --sig_cnt_out                           false
% 19.30/2.98  --trig_cnt_out                          false
% 19.30/2.98  --trig_cnt_out_tolerance                1.
% 19.30/2.98  --trig_cnt_out_sk_spl                   false
% 19.30/2.98  --abstr_cl_out                          false
% 19.30/2.98  
% 19.30/2.98  ------ Global Options
% 19.30/2.98  
% 19.30/2.98  --schedule                              default
% 19.30/2.98  --add_important_lit                     false
% 19.30/2.98  --prop_solver_per_cl                    1000
% 19.30/2.98  --min_unsat_core                        false
% 19.30/2.98  --soft_assumptions                      false
% 19.30/2.98  --soft_lemma_size                       3
% 19.30/2.98  --prop_impl_unit_size                   0
% 19.30/2.98  --prop_impl_unit                        []
% 19.30/2.98  --share_sel_clauses                     true
% 19.30/2.98  --reset_solvers                         false
% 19.30/2.98  --bc_imp_inh                            [conj_cone]
% 19.30/2.98  --conj_cone_tolerance                   3.
% 19.30/2.98  --extra_neg_conj                        none
% 19.30/2.98  --large_theory_mode                     true
% 19.30/2.98  --prolific_symb_bound                   200
% 19.30/2.98  --lt_threshold                          2000
% 19.30/2.98  --clause_weak_htbl                      true
% 19.30/2.98  --gc_record_bc_elim                     false
% 19.30/2.98  
% 19.30/2.98  ------ Preprocessing Options
% 19.30/2.98  
% 19.30/2.98  --preprocessing_flag                    true
% 19.30/2.98  --time_out_prep_mult                    0.1
% 19.30/2.98  --splitting_mode                        input
% 19.30/2.98  --splitting_grd                         true
% 19.30/2.98  --splitting_cvd                         false
% 19.30/2.98  --splitting_cvd_svl                     false
% 19.30/2.98  --splitting_nvd                         32
% 19.30/2.98  --sub_typing                            true
% 19.30/2.98  --prep_gs_sim                           true
% 19.30/2.98  --prep_unflatten                        true
% 19.30/2.98  --prep_res_sim                          true
% 19.30/2.98  --prep_upred                            true
% 19.30/2.98  --prep_sem_filter                       exhaustive
% 19.30/2.98  --prep_sem_filter_out                   false
% 19.30/2.98  --pred_elim                             true
% 19.30/2.98  --res_sim_input                         true
% 19.30/2.98  --eq_ax_congr_red                       true
% 19.30/2.98  --pure_diseq_elim                       true
% 19.30/2.98  --brand_transform                       false
% 19.30/2.98  --non_eq_to_eq                          false
% 19.30/2.98  --prep_def_merge                        true
% 19.30/2.98  --prep_def_merge_prop_impl              false
% 19.30/2.98  --prep_def_merge_mbd                    true
% 19.30/2.98  --prep_def_merge_tr_red                 false
% 19.30/2.98  --prep_def_merge_tr_cl                  false
% 19.30/2.98  --smt_preprocessing                     true
% 19.30/2.98  --smt_ac_axioms                         fast
% 19.30/2.98  --preprocessed_out                      false
% 19.30/2.98  --preprocessed_stats                    false
% 19.30/2.98  
% 19.30/2.98  ------ Abstraction refinement Options
% 19.30/2.98  
% 19.30/2.98  --abstr_ref                             []
% 19.30/2.98  --abstr_ref_prep                        false
% 19.30/2.98  --abstr_ref_until_sat                   false
% 19.30/2.98  --abstr_ref_sig_restrict                funpre
% 19.30/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.30/2.98  --abstr_ref_under                       []
% 19.30/2.98  
% 19.30/2.98  ------ SAT Options
% 19.30/2.98  
% 19.30/2.98  --sat_mode                              false
% 19.30/2.98  --sat_fm_restart_options                ""
% 19.30/2.98  --sat_gr_def                            false
% 19.30/2.98  --sat_epr_types                         true
% 19.30/2.98  --sat_non_cyclic_types                  false
% 19.30/2.98  --sat_finite_models                     false
% 19.30/2.98  --sat_fm_lemmas                         false
% 19.30/2.98  --sat_fm_prep                           false
% 19.30/2.98  --sat_fm_uc_incr                        true
% 19.30/2.98  --sat_out_model                         small
% 19.30/2.98  --sat_out_clauses                       false
% 19.30/2.98  
% 19.30/2.98  ------ QBF Options
% 19.30/2.98  
% 19.30/2.98  --qbf_mode                              false
% 19.30/2.98  --qbf_elim_univ                         false
% 19.30/2.98  --qbf_dom_inst                          none
% 19.30/2.98  --qbf_dom_pre_inst                      false
% 19.30/2.98  --qbf_sk_in                             false
% 19.30/2.98  --qbf_pred_elim                         true
% 19.30/2.98  --qbf_split                             512
% 19.30/2.98  
% 19.30/2.98  ------ BMC1 Options
% 19.30/2.98  
% 19.30/2.98  --bmc1_incremental                      false
% 19.30/2.98  --bmc1_axioms                           reachable_all
% 19.30/2.98  --bmc1_min_bound                        0
% 19.30/2.98  --bmc1_max_bound                        -1
% 19.30/2.98  --bmc1_max_bound_default                -1
% 19.30/2.98  --bmc1_symbol_reachability              true
% 19.30/2.98  --bmc1_property_lemmas                  false
% 19.30/2.98  --bmc1_k_induction                      false
% 19.30/2.98  --bmc1_non_equiv_states                 false
% 19.30/2.98  --bmc1_deadlock                         false
% 19.30/2.98  --bmc1_ucm                              false
% 19.30/2.98  --bmc1_add_unsat_core                   none
% 19.30/2.98  --bmc1_unsat_core_children              false
% 19.30/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.30/2.98  --bmc1_out_stat                         full
% 19.30/2.98  --bmc1_ground_init                      false
% 19.30/2.98  --bmc1_pre_inst_next_state              false
% 19.30/2.98  --bmc1_pre_inst_state                   false
% 19.30/2.98  --bmc1_pre_inst_reach_state             false
% 19.30/2.98  --bmc1_out_unsat_core                   false
% 19.30/2.98  --bmc1_aig_witness_out                  false
% 19.30/2.98  --bmc1_verbose                          false
% 19.30/2.98  --bmc1_dump_clauses_tptp                false
% 19.30/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.30/2.98  --bmc1_dump_file                        -
% 19.30/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.30/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.30/2.98  --bmc1_ucm_extend_mode                  1
% 19.30/2.98  --bmc1_ucm_init_mode                    2
% 19.30/2.98  --bmc1_ucm_cone_mode                    none
% 19.30/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.30/2.98  --bmc1_ucm_relax_model                  4
% 19.30/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.30/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.30/2.98  --bmc1_ucm_layered_model                none
% 19.30/2.98  --bmc1_ucm_max_lemma_size               10
% 19.30/2.98  
% 19.30/2.98  ------ AIG Options
% 19.30/2.98  
% 19.30/2.98  --aig_mode                              false
% 19.30/2.98  
% 19.30/2.98  ------ Instantiation Options
% 19.30/2.98  
% 19.30/2.98  --instantiation_flag                    true
% 19.30/2.98  --inst_sos_flag                         true
% 19.30/2.98  --inst_sos_phase                        true
% 19.30/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.30/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.30/2.98  --inst_lit_sel_side                     num_symb
% 19.30/2.98  --inst_solver_per_active                1400
% 19.30/2.98  --inst_solver_calls_frac                1.
% 19.30/2.98  --inst_passive_queue_type               priority_queues
% 19.30/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.30/2.98  --inst_passive_queues_freq              [25;2]
% 19.30/2.98  --inst_dismatching                      true
% 19.30/2.98  --inst_eager_unprocessed_to_passive     true
% 19.30/2.98  --inst_prop_sim_given                   true
% 19.30/2.98  --inst_prop_sim_new                     false
% 19.30/2.98  --inst_subs_new                         false
% 19.30/2.98  --inst_eq_res_simp                      false
% 19.30/2.98  --inst_subs_given                       false
% 19.30/2.98  --inst_orphan_elimination               true
% 19.30/2.98  --inst_learning_loop_flag               true
% 19.30/2.98  --inst_learning_start                   3000
% 19.30/2.98  --inst_learning_factor                  2
% 19.30/2.98  --inst_start_prop_sim_after_learn       3
% 19.30/2.98  --inst_sel_renew                        solver
% 19.30/2.98  --inst_lit_activity_flag                true
% 19.30/2.98  --inst_restr_to_given                   false
% 19.30/2.98  --inst_activity_threshold               500
% 19.30/2.98  --inst_out_proof                        true
% 19.30/2.98  
% 19.30/2.98  ------ Resolution Options
% 19.30/2.98  
% 19.30/2.98  --resolution_flag                       true
% 19.30/2.98  --res_lit_sel                           adaptive
% 19.30/2.98  --res_lit_sel_side                      none
% 19.30/2.98  --res_ordering                          kbo
% 19.30/2.98  --res_to_prop_solver                    active
% 19.30/2.98  --res_prop_simpl_new                    false
% 19.30/2.98  --res_prop_simpl_given                  true
% 19.30/2.98  --res_passive_queue_type                priority_queues
% 19.30/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.30/2.98  --res_passive_queues_freq               [15;5]
% 19.30/2.98  --res_forward_subs                      full
% 19.30/2.98  --res_backward_subs                     full
% 19.30/2.98  --res_forward_subs_resolution           true
% 19.30/2.98  --res_backward_subs_resolution          true
% 19.30/2.98  --res_orphan_elimination                true
% 19.30/2.98  --res_time_limit                        2.
% 19.30/2.98  --res_out_proof                         true
% 19.30/2.98  
% 19.30/2.98  ------ Superposition Options
% 19.30/2.98  
% 19.30/2.98  --superposition_flag                    true
% 19.30/2.98  --sup_passive_queue_type                priority_queues
% 19.30/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.30/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.30/2.98  --demod_completeness_check              fast
% 19.30/2.98  --demod_use_ground                      true
% 19.30/2.98  --sup_to_prop_solver                    passive
% 19.30/2.98  --sup_prop_simpl_new                    true
% 19.30/2.98  --sup_prop_simpl_given                  true
% 19.30/2.98  --sup_fun_splitting                     true
% 19.30/2.98  --sup_smt_interval                      50000
% 19.30/2.98  
% 19.30/2.98  ------ Superposition Simplification Setup
% 19.30/2.98  
% 19.30/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.30/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.30/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.30/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.30/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.30/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.30/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.30/2.98  --sup_immed_triv                        [TrivRules]
% 19.30/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.98  --sup_immed_bw_main                     []
% 19.30/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.30/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.30/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.98  --sup_input_bw                          []
% 19.30/2.98  
% 19.30/2.98  ------ Combination Options
% 19.30/2.98  
% 19.30/2.98  --comb_res_mult                         3
% 19.30/2.98  --comb_sup_mult                         2
% 19.30/2.98  --comb_inst_mult                        10
% 19.30/2.98  
% 19.30/2.98  ------ Debug Options
% 19.30/2.98  
% 19.30/2.98  --dbg_backtrace                         false
% 19.30/2.98  --dbg_dump_prop_clauses                 false
% 19.30/2.98  --dbg_dump_prop_clauses_file            -
% 19.30/2.98  --dbg_out_stat                          false
% 19.30/2.98  ------ Parsing...
% 19.30/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.30/2.98  
% 19.30/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 19.30/2.98  
% 19.30/2.98  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.30/2.98  
% 19.30/2.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.30/2.98  ------ Proving...
% 19.30/2.98  ------ Problem Properties 
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  clauses                                 21
% 19.30/2.98  conjectures                             1
% 19.30/2.98  EPR                                     1
% 19.30/2.98  Horn                                    19
% 19.30/2.98  unary                                   3
% 19.30/2.98  binary                                  13
% 19.30/2.98  lits                                    45
% 19.30/2.98  lits eq                                 14
% 19.30/2.98  fd_pure                                 0
% 19.30/2.98  fd_pseudo                               0
% 19.30/2.98  fd_cond                                 0
% 19.30/2.98  fd_pseudo_cond                          0
% 19.30/2.98  AC symbols                              0
% 19.30/2.98  
% 19.30/2.98  ------ Schedule dynamic 5 is on 
% 19.30/2.98  
% 19.30/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  ------ 
% 19.30/2.98  Current options:
% 19.30/2.98  ------ 
% 19.30/2.98  
% 19.30/2.98  ------ Input Options
% 19.30/2.98  
% 19.30/2.98  --out_options                           all
% 19.30/2.98  --tptp_safe_out                         true
% 19.30/2.98  --problem_path                          ""
% 19.30/2.98  --include_path                          ""
% 19.30/2.98  --clausifier                            res/vclausify_rel
% 19.30/2.98  --clausifier_options                    ""
% 19.30/2.98  --stdin                                 false
% 19.30/2.98  --stats_out                             all
% 19.30/2.98  
% 19.30/2.98  ------ General Options
% 19.30/2.98  
% 19.30/2.98  --fof                                   false
% 19.30/2.98  --time_out_real                         305.
% 19.30/2.98  --time_out_virtual                      -1.
% 19.30/2.98  --symbol_type_check                     false
% 19.30/2.98  --clausify_out                          false
% 19.30/2.98  --sig_cnt_out                           false
% 19.30/2.98  --trig_cnt_out                          false
% 19.30/2.98  --trig_cnt_out_tolerance                1.
% 19.30/2.98  --trig_cnt_out_sk_spl                   false
% 19.30/2.98  --abstr_cl_out                          false
% 19.30/2.98  
% 19.30/2.98  ------ Global Options
% 19.30/2.98  
% 19.30/2.98  --schedule                              default
% 19.30/2.98  --add_important_lit                     false
% 19.30/2.98  --prop_solver_per_cl                    1000
% 19.30/2.98  --min_unsat_core                        false
% 19.30/2.98  --soft_assumptions                      false
% 19.30/2.98  --soft_lemma_size                       3
% 19.30/2.98  --prop_impl_unit_size                   0
% 19.30/2.98  --prop_impl_unit                        []
% 19.30/2.98  --share_sel_clauses                     true
% 19.30/2.98  --reset_solvers                         false
% 19.30/2.98  --bc_imp_inh                            [conj_cone]
% 19.30/2.98  --conj_cone_tolerance                   3.
% 19.30/2.98  --extra_neg_conj                        none
% 19.30/2.98  --large_theory_mode                     true
% 19.30/2.98  --prolific_symb_bound                   200
% 19.30/2.98  --lt_threshold                          2000
% 19.30/2.98  --clause_weak_htbl                      true
% 19.30/2.98  --gc_record_bc_elim                     false
% 19.30/2.98  
% 19.30/2.98  ------ Preprocessing Options
% 19.30/2.98  
% 19.30/2.98  --preprocessing_flag                    true
% 19.30/2.98  --time_out_prep_mult                    0.1
% 19.30/2.98  --splitting_mode                        input
% 19.30/2.98  --splitting_grd                         true
% 19.30/2.98  --splitting_cvd                         false
% 19.30/2.98  --splitting_cvd_svl                     false
% 19.30/2.98  --splitting_nvd                         32
% 19.30/2.98  --sub_typing                            true
% 19.30/2.98  --prep_gs_sim                           true
% 19.30/2.98  --prep_unflatten                        true
% 19.30/2.98  --prep_res_sim                          true
% 19.30/2.98  --prep_upred                            true
% 19.30/2.98  --prep_sem_filter                       exhaustive
% 19.30/2.98  --prep_sem_filter_out                   false
% 19.30/2.98  --pred_elim                             true
% 19.30/2.98  --res_sim_input                         true
% 19.30/2.98  --eq_ax_congr_red                       true
% 19.30/2.98  --pure_diseq_elim                       true
% 19.30/2.98  --brand_transform                       false
% 19.30/2.98  --non_eq_to_eq                          false
% 19.30/2.98  --prep_def_merge                        true
% 19.30/2.98  --prep_def_merge_prop_impl              false
% 19.30/2.98  --prep_def_merge_mbd                    true
% 19.30/2.98  --prep_def_merge_tr_red                 false
% 19.30/2.98  --prep_def_merge_tr_cl                  false
% 19.30/2.98  --smt_preprocessing                     true
% 19.30/2.98  --smt_ac_axioms                         fast
% 19.30/2.98  --preprocessed_out                      false
% 19.30/2.98  --preprocessed_stats                    false
% 19.30/2.98  
% 19.30/2.98  ------ Abstraction refinement Options
% 19.30/2.98  
% 19.30/2.98  --abstr_ref                             []
% 19.30/2.98  --abstr_ref_prep                        false
% 19.30/2.98  --abstr_ref_until_sat                   false
% 19.30/2.98  --abstr_ref_sig_restrict                funpre
% 19.30/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.30/2.98  --abstr_ref_under                       []
% 19.30/2.98  
% 19.30/2.98  ------ SAT Options
% 19.30/2.98  
% 19.30/2.98  --sat_mode                              false
% 19.30/2.98  --sat_fm_restart_options                ""
% 19.30/2.98  --sat_gr_def                            false
% 19.30/2.98  --sat_epr_types                         true
% 19.30/2.98  --sat_non_cyclic_types                  false
% 19.30/2.98  --sat_finite_models                     false
% 19.30/2.98  --sat_fm_lemmas                         false
% 19.30/2.98  --sat_fm_prep                           false
% 19.30/2.98  --sat_fm_uc_incr                        true
% 19.30/2.98  --sat_out_model                         small
% 19.30/2.98  --sat_out_clauses                       false
% 19.30/2.98  
% 19.30/2.98  ------ QBF Options
% 19.30/2.98  
% 19.30/2.98  --qbf_mode                              false
% 19.30/2.98  --qbf_elim_univ                         false
% 19.30/2.98  --qbf_dom_inst                          none
% 19.30/2.98  --qbf_dom_pre_inst                      false
% 19.30/2.98  --qbf_sk_in                             false
% 19.30/2.98  --qbf_pred_elim                         true
% 19.30/2.98  --qbf_split                             512
% 19.30/2.98  
% 19.30/2.98  ------ BMC1 Options
% 19.30/2.98  
% 19.30/2.98  --bmc1_incremental                      false
% 19.30/2.98  --bmc1_axioms                           reachable_all
% 19.30/2.98  --bmc1_min_bound                        0
% 19.30/2.98  --bmc1_max_bound                        -1
% 19.30/2.98  --bmc1_max_bound_default                -1
% 19.30/2.98  --bmc1_symbol_reachability              true
% 19.30/2.98  --bmc1_property_lemmas                  false
% 19.30/2.98  --bmc1_k_induction                      false
% 19.30/2.98  --bmc1_non_equiv_states                 false
% 19.30/2.98  --bmc1_deadlock                         false
% 19.30/2.98  --bmc1_ucm                              false
% 19.30/2.98  --bmc1_add_unsat_core                   none
% 19.30/2.98  --bmc1_unsat_core_children              false
% 19.30/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.30/2.98  --bmc1_out_stat                         full
% 19.30/2.98  --bmc1_ground_init                      false
% 19.30/2.98  --bmc1_pre_inst_next_state              false
% 19.30/2.98  --bmc1_pre_inst_state                   false
% 19.30/2.98  --bmc1_pre_inst_reach_state             false
% 19.30/2.98  --bmc1_out_unsat_core                   false
% 19.30/2.98  --bmc1_aig_witness_out                  false
% 19.30/2.98  --bmc1_verbose                          false
% 19.30/2.98  --bmc1_dump_clauses_tptp                false
% 19.30/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.30/2.98  --bmc1_dump_file                        -
% 19.30/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.30/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.30/2.98  --bmc1_ucm_extend_mode                  1
% 19.30/2.98  --bmc1_ucm_init_mode                    2
% 19.30/2.98  --bmc1_ucm_cone_mode                    none
% 19.30/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.30/2.98  --bmc1_ucm_relax_model                  4
% 19.30/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.30/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.30/2.98  --bmc1_ucm_layered_model                none
% 19.30/2.98  --bmc1_ucm_max_lemma_size               10
% 19.30/2.98  
% 19.30/2.98  ------ AIG Options
% 19.30/2.98  
% 19.30/2.98  --aig_mode                              false
% 19.30/2.98  
% 19.30/2.98  ------ Instantiation Options
% 19.30/2.98  
% 19.30/2.98  --instantiation_flag                    true
% 19.30/2.98  --inst_sos_flag                         true
% 19.30/2.98  --inst_sos_phase                        true
% 19.30/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.30/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.30/2.98  --inst_lit_sel_side                     none
% 19.30/2.98  --inst_solver_per_active                1400
% 19.30/2.98  --inst_solver_calls_frac                1.
% 19.30/2.98  --inst_passive_queue_type               priority_queues
% 19.30/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.30/2.98  --inst_passive_queues_freq              [25;2]
% 19.30/2.98  --inst_dismatching                      true
% 19.30/2.98  --inst_eager_unprocessed_to_passive     true
% 19.30/2.98  --inst_prop_sim_given                   true
% 19.30/2.98  --inst_prop_sim_new                     false
% 19.30/2.98  --inst_subs_new                         false
% 19.30/2.98  --inst_eq_res_simp                      false
% 19.30/2.98  --inst_subs_given                       false
% 19.30/2.98  --inst_orphan_elimination               true
% 19.30/2.98  --inst_learning_loop_flag               true
% 19.30/2.98  --inst_learning_start                   3000
% 19.30/2.98  --inst_learning_factor                  2
% 19.30/2.98  --inst_start_prop_sim_after_learn       3
% 19.30/2.98  --inst_sel_renew                        solver
% 19.30/2.98  --inst_lit_activity_flag                true
% 19.30/2.98  --inst_restr_to_given                   false
% 19.30/2.98  --inst_activity_threshold               500
% 19.30/2.98  --inst_out_proof                        true
% 19.30/2.98  
% 19.30/2.98  ------ Resolution Options
% 19.30/2.98  
% 19.30/2.98  --resolution_flag                       false
% 19.30/2.98  --res_lit_sel                           adaptive
% 19.30/2.98  --res_lit_sel_side                      none
% 19.30/2.98  --res_ordering                          kbo
% 19.30/2.98  --res_to_prop_solver                    active
% 19.30/2.98  --res_prop_simpl_new                    false
% 19.30/2.98  --res_prop_simpl_given                  true
% 19.30/2.98  --res_passive_queue_type                priority_queues
% 19.30/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.30/2.98  --res_passive_queues_freq               [15;5]
% 19.30/2.98  --res_forward_subs                      full
% 19.30/2.98  --res_backward_subs                     full
% 19.30/2.98  --res_forward_subs_resolution           true
% 19.30/2.98  --res_backward_subs_resolution          true
% 19.30/2.98  --res_orphan_elimination                true
% 19.30/2.98  --res_time_limit                        2.
% 19.30/2.98  --res_out_proof                         true
% 19.30/2.98  
% 19.30/2.98  ------ Superposition Options
% 19.30/2.98  
% 19.30/2.98  --superposition_flag                    true
% 19.30/2.98  --sup_passive_queue_type                priority_queues
% 19.30/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.30/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.30/2.98  --demod_completeness_check              fast
% 19.30/2.98  --demod_use_ground                      true
% 19.30/2.98  --sup_to_prop_solver                    passive
% 19.30/2.98  --sup_prop_simpl_new                    true
% 19.30/2.98  --sup_prop_simpl_given                  true
% 19.30/2.98  --sup_fun_splitting                     true
% 19.30/2.98  --sup_smt_interval                      50000
% 19.30/2.98  
% 19.30/2.98  ------ Superposition Simplification Setup
% 19.30/2.98  
% 19.30/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.30/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.30/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.30/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.30/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.30/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.30/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.30/2.98  --sup_immed_triv                        [TrivRules]
% 19.30/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.98  --sup_immed_bw_main                     []
% 19.30/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.30/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.30/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.98  --sup_input_bw                          []
% 19.30/2.98  
% 19.30/2.98  ------ Combination Options
% 19.30/2.98  
% 19.30/2.98  --comb_res_mult                         3
% 19.30/2.98  --comb_sup_mult                         2
% 19.30/2.98  --comb_inst_mult                        10
% 19.30/2.98  
% 19.30/2.98  ------ Debug Options
% 19.30/2.98  
% 19.30/2.98  --dbg_backtrace                         false
% 19.30/2.98  --dbg_dump_prop_clauses                 false
% 19.30/2.98  --dbg_dump_prop_clauses_file            -
% 19.30/2.98  --dbg_out_stat                          false
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  ------ Proving...
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  % SZS status Theorem for theBenchmark.p
% 19.30/2.98  
% 19.30/2.98   Resolution empty clause
% 19.30/2.98  
% 19.30/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.30/2.98  
% 19.30/2.98  fof(f16,conjecture,(
% 19.30/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f17,negated_conjecture,(
% 19.30/2.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 19.30/2.98    inference(negated_conjecture,[],[f16])).
% 19.30/2.98  
% 19.30/2.98  fof(f35,plain,(
% 19.30/2.98    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f17])).
% 19.30/2.98  
% 19.30/2.98  fof(f36,plain,(
% 19.30/2.98    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.30/2.98    inference(flattening,[],[f35])).
% 19.30/2.98  
% 19.30/2.98  fof(f37,plain,(
% 19.30/2.98    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.30/2.98    inference(nnf_transformation,[],[f36])).
% 19.30/2.98  
% 19.30/2.98  fof(f38,plain,(
% 19.30/2.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.30/2.98    inference(flattening,[],[f37])).
% 19.30/2.98  
% 19.30/2.98  fof(f40,plain,(
% 19.30/2.98    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) != k2_tops_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) = k2_tops_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.30/2.98    introduced(choice_axiom,[])).
% 19.30/2.98  
% 19.30/2.98  fof(f39,plain,(
% 19.30/2.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) != k2_tops_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) = k2_tops_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 19.30/2.98    introduced(choice_axiom,[])).
% 19.30/2.98  
% 19.30/2.98  fof(f41,plain,(
% 19.30/2.98    ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 19.30/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 19.30/2.98  
% 19.30/2.98  fof(f61,plain,(
% 19.30/2.98    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 19.30/2.98    inference(cnf_transformation,[],[f41])).
% 19.30/2.98  
% 19.30/2.98  fof(f14,axiom,(
% 19.30/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f32,plain,(
% 19.30/2.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f14])).
% 19.30/2.98  
% 19.30/2.98  fof(f33,plain,(
% 19.30/2.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.30/2.98    inference(flattening,[],[f32])).
% 19.30/2.98  
% 19.30/2.98  fof(f55,plain,(
% 19.30/2.98    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f33])).
% 19.30/2.98  
% 19.30/2.98  fof(f58,plain,(
% 19.30/2.98    v2_pre_topc(sK0)),
% 19.30/2.98    inference(cnf_transformation,[],[f41])).
% 19.30/2.98  
% 19.30/2.98  fof(f59,plain,(
% 19.30/2.98    l1_pre_topc(sK0)),
% 19.30/2.98    inference(cnf_transformation,[],[f41])).
% 19.30/2.98  
% 19.30/2.98  fof(f60,plain,(
% 19.30/2.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.30/2.98    inference(cnf_transformation,[],[f41])).
% 19.30/2.98  
% 19.30/2.98  fof(f12,axiom,(
% 19.30/2.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f29,plain,(
% 19.30/2.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f12])).
% 19.30/2.98  
% 19.30/2.98  fof(f30,plain,(
% 19.30/2.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.30/2.98    inference(flattening,[],[f29])).
% 19.30/2.98  
% 19.30/2.98  fof(f53,plain,(
% 19.30/2.98    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f30])).
% 19.30/2.98  
% 19.30/2.98  fof(f10,axiom,(
% 19.30/2.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f26,plain,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f10])).
% 19.30/2.98  
% 19.30/2.98  fof(f27,plain,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.30/2.98    inference(flattening,[],[f26])).
% 19.30/2.98  
% 19.30/2.98  fof(f51,plain,(
% 19.30/2.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f27])).
% 19.30/2.98  
% 19.30/2.98  fof(f7,axiom,(
% 19.30/2.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f23,plain,(
% 19.30/2.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f7])).
% 19.30/2.98  
% 19.30/2.98  fof(f48,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.30/2.98    inference(cnf_transformation,[],[f23])).
% 19.30/2.98  
% 19.30/2.98  fof(f9,axiom,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f18,plain,(
% 19.30/2.98    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 19.30/2.98    inference(unused_predicate_definition_removal,[],[f9])).
% 19.30/2.98  
% 19.30/2.98  fof(f25,plain,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 19.30/2.98    inference(ennf_transformation,[],[f18])).
% 19.30/2.98  
% 19.30/2.98  fof(f50,plain,(
% 19.30/2.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f25])).
% 19.30/2.98  
% 19.30/2.98  fof(f11,axiom,(
% 19.30/2.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f28,plain,(
% 19.30/2.98    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.30/2.98    inference(ennf_transformation,[],[f11])).
% 19.30/2.98  
% 19.30/2.98  fof(f52,plain,(
% 19.30/2.98    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f28])).
% 19.30/2.98  
% 19.30/2.98  fof(f4,axiom,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f20,plain,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f4])).
% 19.30/2.98  
% 19.30/2.98  fof(f45,plain,(
% 19.30/2.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.30/2.98    inference(cnf_transformation,[],[f20])).
% 19.30/2.98  
% 19.30/2.98  fof(f8,axiom,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f24,plain,(
% 19.30/2.98    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f8])).
% 19.30/2.98  
% 19.30/2.98  fof(f49,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.30/2.98    inference(cnf_transformation,[],[f24])).
% 19.30/2.98  
% 19.30/2.98  fof(f2,axiom,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f19,plain,(
% 19.30/2.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f2])).
% 19.30/2.98  
% 19.30/2.98  fof(f43,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.30/2.98    inference(cnf_transformation,[],[f19])).
% 19.30/2.98  
% 19.30/2.98  fof(f6,axiom,(
% 19.30/2.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f22,plain,(
% 19.30/2.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f6])).
% 19.30/2.98  
% 19.30/2.98  fof(f47,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.30/2.98    inference(cnf_transformation,[],[f22])).
% 19.30/2.98  
% 19.30/2.98  fof(f3,axiom,(
% 19.30/2.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f44,plain,(
% 19.30/2.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 19.30/2.98    inference(cnf_transformation,[],[f3])).
% 19.30/2.98  
% 19.30/2.98  fof(f5,axiom,(
% 19.30/2.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f21,plain,(
% 19.30/2.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.30/2.98    inference(ennf_transformation,[],[f5])).
% 19.30/2.98  
% 19.30/2.98  fof(f46,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.30/2.98    inference(cnf_transformation,[],[f21])).
% 19.30/2.98  
% 19.30/2.98  fof(f15,axiom,(
% 19.30/2.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f34,plain,(
% 19.30/2.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.30/2.98    inference(ennf_transformation,[],[f15])).
% 19.30/2.98  
% 19.30/2.98  fof(f57,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f34])).
% 19.30/2.98  
% 19.30/2.98  fof(f62,plain,(
% 19.30/2.98    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 19.30/2.98    inference(cnf_transformation,[],[f41])).
% 19.30/2.98  
% 19.30/2.98  fof(f56,plain,(
% 19.30/2.98    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f33])).
% 19.30/2.98  
% 19.30/2.98  fof(f13,axiom,(
% 19.30/2.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f31,plain,(
% 19.30/2.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.30/2.98    inference(ennf_transformation,[],[f13])).
% 19.30/2.98  
% 19.30/2.98  fof(f54,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f31])).
% 19.30/2.98  
% 19.30/2.98  cnf(c_17,negated_conjecture,
% 19.30/2.98      ( v3_pre_topc(sK1,sK0)
% 19.30/2.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 19.30/2.98      inference(cnf_transformation,[],[f61]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_168,plain,
% 19.30/2.98      ( v3_pre_topc(sK1,sK0)
% 19.30/2.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 19.30/2.98      inference(prop_impl,[status(thm)],[c_17]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_14,plain,
% 19.30/2.98      ( ~ v3_pre_topc(X0,X1)
% 19.30/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 19.30/2.98      | ~ v2_pre_topc(X3)
% 19.30/2.98      | ~ l1_pre_topc(X3)
% 19.30/2.98      | ~ l1_pre_topc(X1)
% 19.30/2.98      | k1_tops_1(X1,X0) = X0 ),
% 19.30/2.98      inference(cnf_transformation,[],[f55]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_20,negated_conjecture,
% 19.30/2.98      ( v2_pre_topc(sK0) ),
% 19.30/2.98      inference(cnf_transformation,[],[f58]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_360,plain,
% 19.30/2.98      ( ~ v3_pre_topc(X0,X1)
% 19.30/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 19.30/2.98      | ~ l1_pre_topc(X1)
% 19.30/2.98      | ~ l1_pre_topc(X3)
% 19.30/2.98      | k1_tops_1(X1,X0) = X0
% 19.30/2.98      | sK0 != X3 ),
% 19.30/2.98      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_361,plain,
% 19.30/2.98      ( ~ v3_pre_topc(X0,X1)
% 19.30/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.98      | ~ l1_pre_topc(X1)
% 19.30/2.98      | ~ l1_pre_topc(sK0)
% 19.30/2.98      | k1_tops_1(X1,X0) = X0 ),
% 19.30/2.98      inference(unflattening,[status(thm)],[c_360]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_19,negated_conjecture,
% 19.30/2.98      ( l1_pre_topc(sK0) ),
% 19.30/2.98      inference(cnf_transformation,[],[f59]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_365,plain,
% 19.30/2.98      ( ~ l1_pre_topc(X1)
% 19.30/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.98      | ~ v3_pre_topc(X0,X1)
% 19.30/2.98      | k1_tops_1(X1,X0) = X0 ),
% 19.30/2.98      inference(global_propositional_subsumption,[status(thm)],[c_361,c_19]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_366,plain,
% 19.30/2.98      ( ~ v3_pre_topc(X0,X1)
% 19.30/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.98      | ~ l1_pre_topc(X1)
% 19.30/2.98      | k1_tops_1(X1,X0) = X0 ),
% 19.30/2.98      inference(renaming,[status(thm)],[c_365]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_400,plain,
% 19.30/2.98      ( ~ v3_pre_topc(X0,X1)
% 19.30/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.98      | k1_tops_1(X1,X0) = X0
% 19.30/2.98      | sK0 != X1 ),
% 19.30/2.98      inference(resolution_lifted,[status(thm)],[c_366,c_19]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_401,plain,
% 19.30/2.99      ( ~ v3_pre_topc(X0,sK0)
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k1_tops_1(sK0,X0) = X0 ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_400]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_525,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,X1) = X1
% 19.30/2.99      | sK1 != X1
% 19.30/2.99      | sK0 != sK0 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_168,c_401]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_526,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) = sK1 ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_525]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_18,negated_conjecture,
% 19.30/2.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.30/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_530,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) = sK1 ),
% 19.30/2.99      inference(global_propositional_subsumption,[status(thm)],[c_526,c_18]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_733,plain,
% 19.30/2.99      ( sP0_iProver_split
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) = sK1 ),
% 19.30/2.99      inference(splitting,
% 19.30/2.99                [splitting(split),new_symbols(definition,[])],
% 19.30/2.99                [c_530]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1058,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) = sK1
% 19.30/2.99      | sP0_iProver_split = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1065,plain,
% 19.30/2.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_11,plain,
% 19.30/2.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.30/2.99      | ~ v2_pre_topc(X0)
% 19.30/2.99      | ~ l1_pre_topc(X0) ),
% 19.30/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_317,plain,
% 19.30/2.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.30/2.99      | ~ l1_pre_topc(X0)
% 19.30/2.99      | sK0 != X0 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_318,plain,
% 19.30/2.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ l1_pre_topc(sK0) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_317]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_322,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 19.30/2.99      inference(global_propositional_subsumption,[status(thm)],[c_318,c_19]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_323,plain,
% 19.30/2.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.30/2.99      inference(renaming,[status(thm)],[c_322]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_567,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k1_tops_1(sK0,X1) != X0
% 19.30/2.99      | k1_tops_1(sK0,X0) = X0
% 19.30/2.99      | sK0 != sK0 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_323,c_401]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_568,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_567]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_729,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~ sP0_iProver_split ),
% 19.30/2.99      inference(splitting,
% 19.30/2.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 19.30/2.99                [c_568]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1055,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.30/2.99      | sP0_iProver_split != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1373,plain,
% 19.30/2.99      ( sP0_iProver_split != iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_1055]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1375,plain,
% 19.30/2.99      ( ~ sP0_iProver_split ),
% 19.30/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_1373]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3832,plain,
% 19.30/2.99      ( k1_tops_1(sK0,sK1) = sK1
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(global_propositional_subsumption,
% 19.30/2.99                [status(thm)],
% 19.30/2.99                [c_1058,c_733,c_1375]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3833,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) = sK1 ),
% 19.30/2.99      inference(renaming,[status(thm)],[c_3832]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_9,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | ~ l1_pre_topc(X1) ),
% 19.30/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_454,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | sK0 != X1 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_455,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_454]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1060,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.30/2.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_6,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.30/2.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 19.30/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1067,plain,
% 19.30/2.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 19.30/2.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2306,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1060,c_1067]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3819,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_2306]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3834,plain,
% 19.30/2.99      ( k1_tops_1(sK0,sK1) = sK1
% 19.30/2.99      | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_3833,c_3819]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_8,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.30/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_10,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 19.30/2.99      | ~ l1_pre_topc(X1) ),
% 19.30/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_296,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.30/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 19.30/2.99      | ~ l1_pre_topc(X3)
% 19.30/2.99      | X2 != X0
% 19.30/2.99      | k2_pre_topc(X3,X2) != X1 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_297,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(X1,X0)))
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | ~ l1_pre_topc(X1) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_296]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_418,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(X1,X0)))
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | sK0 != X1 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_297,c_19]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_419,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK0,X0)))
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_418]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1063,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_pre_topc(sK0,X0))) = iProver_top
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.30/2.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 19.30/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1070,plain,
% 19.30/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.30/2.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_7,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.30/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.30/2.99      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 19.30/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1066,plain,
% 19.30/2.99      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 19.30/2.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 19.30/2.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2432,plain,
% 19.30/2.99      ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X1)) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1)
% 19.30/2.99      | m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,X0))) != iProver_top
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1063,c_1066]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_9754,plain,
% 19.30/2.99      ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X1))) = k7_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X1))
% 19.30/2.99      | m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,X0))) != iProver_top
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1070,c_2432]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69160,plain,
% 19.30/2.99      ( k9_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0))) = k7_subset_1(k2_pre_topc(sK0,X0),X0,k3_subset_1(k2_pre_topc(sK0,X0),X0))
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1063,c_9754]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69372,plain,
% 19.30/2.99      ( k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_69160]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.30/2.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 19.30/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1072,plain,
% 19.30/2.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 19.30/2.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1603,plain,
% 19.30/2.99      ( k3_subset_1(k2_pre_topc(sK0,X0),X0) = k4_xboole_0(k2_pre_topc(sK0,X0),X0)
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1063,c_1072]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2180,plain,
% 19.30/2.99      ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_1603]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_5,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.30/2.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 19.30/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1068,plain,
% 19.30/2.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 19.30/2.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1522,plain,
% 19.30/2.99      ( k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0)) = X0
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1063,c_1068]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1895,plain,
% 19.30/2.99      ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_1522]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2556,plain,
% 19.30/2.99      ( k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_2180,c_1895]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69398,plain,
% 19.30/2.99      ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) ),
% 19.30/2.99      inference(light_normalisation,[status(thm)],[c_69372,c_2180,c_2556]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2,plain,
% 19.30/2.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 19.30/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1071,plain,
% 19.30/2.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_4,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 19.30/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1069,plain,
% 19.30/2.99      ( k9_subset_1(X0,X1,X1) = X1
% 19.30/2.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1513,plain,
% 19.30/2.99      ( k9_subset_1(X0,X1,X1) = X1 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1071,c_1069]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2305,plain,
% 19.30/2.99      ( k7_subset_1(k2_pre_topc(sK0,X0),X0,X1) = k4_xboole_0(X0,X1)
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1063,c_1067]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2737,plain,
% 19.30/2.99      ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_2305]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69399,plain,
% 19.30/2.99      ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_69398,c_1513,c_2737]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69411,plain,
% 19.30/2.99      ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = sK1
% 19.30/2.99      | k1_tops_1(sK0,sK1) = sK1 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_3834,c_69399]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_15,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | ~ l1_pre_topc(X1)
% 19.30/2.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 19.30/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_430,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 19.30/2.99      | sK0 != X1 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_431,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_430]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1062,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1251,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_1062]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2304,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_1067]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_2554,plain,
% 19.30/2.99      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1251,c_2304]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69413,plain,
% 19.30/2.99      ( k1_tops_1(sK0,sK1) = sK1 ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_69411,c_2554,c_2737]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_16,negated_conjecture,
% 19.30/2.99      ( ~ v3_pre_topc(sK1,sK0)
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_166,plain,
% 19.30/2.99      ( ~ v3_pre_topc(sK1,sK0)
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_13,plain,
% 19.30/2.99      ( v3_pre_topc(X0,X1)
% 19.30/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | ~ v2_pre_topc(X1)
% 19.30/2.99      | ~ l1_pre_topc(X1)
% 19.30/2.99      | ~ l1_pre_topc(X3)
% 19.30/2.99      | k1_tops_1(X1,X0) != X0 ),
% 19.30/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_335,plain,
% 19.30/2.99      ( v3_pre_topc(X0,X1)
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 19.30/2.99      | ~ l1_pre_topc(X1)
% 19.30/2.99      | ~ l1_pre_topc(X3)
% 19.30/2.99      | k1_tops_1(X1,X0) != X0
% 19.30/2.99      | sK0 != X1 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_336,plain,
% 19.30/2.99      ( v3_pre_topc(X0,sK0)
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ l1_pre_topc(X2)
% 19.30/2.99      | ~ l1_pre_topc(sK0)
% 19.30/2.99      | k1_tops_1(sK0,X0) != X0 ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_335]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_340,plain,
% 19.30/2.99      ( ~ l1_pre_topc(X2)
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 19.30/2.99      | v3_pre_topc(X0,sK0)
% 19.30/2.99      | k1_tops_1(sK0,X0) != X0 ),
% 19.30/2.99      inference(global_propositional_subsumption,[status(thm)],[c_336,c_19]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_341,plain,
% 19.30/2.99      ( v3_pre_topc(X0,sK0)
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ l1_pre_topc(X2)
% 19.30/2.99      | k1_tops_1(sK0,X0) != X0 ),
% 19.30/2.99      inference(renaming,[status(thm)],[c_340]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_466,plain,
% 19.30/2.99      ( v3_pre_topc(X0,sK0)
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k1_tops_1(sK0,X0) != X0
% 19.30/2.99      | sK0 != X2 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_19,c_341]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_467,plain,
% 19.30/2.99      ( v3_pre_topc(X0,sK0)
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k1_tops_1(sK0,X0) != X0 ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_466]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_546,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,X1) != X1
% 19.30/2.99      | sK1 != X1
% 19.30/2.99      | sK0 != sK0 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_166,c_467]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_547,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) != sK1 ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_546]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_551,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) != sK1 ),
% 19.30/2.99      inference(global_propositional_subsumption,[status(thm)],[c_547,c_18]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_732,plain,
% 19.30/2.99      ( sP0_iProver_split
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) != sK1 ),
% 19.30/2.99      inference(splitting,
% 19.30/2.99                [splitting(split),new_symbols(definition,[])],
% 19.30/2.99                [c_551]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1056,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) != sK1
% 19.30/2.99      | sP0_iProver_split = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3046,plain,
% 19.30/2.99      ( k1_tops_1(sK0,sK1) != sK1
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(global_propositional_subsumption,
% 19.30/2.99                [status(thm)],
% 19.30/2.99                [c_1056,c_732,c_1375]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3047,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 19.30/2.99      | k1_tops_1(sK0,sK1) != sK1 ),
% 19.30/2.99      inference(renaming,[status(thm)],[c_3046]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3920,plain,
% 19.30/2.99      ( k1_tops_1(sK0,sK1) != sK1
% 19.30/2.99      | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_3819,c_3047]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69542,plain,
% 19.30/2.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 19.30/2.99      | sK1 != sK1 ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_69413,c_3920]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69547,plain,
% 19.30/2.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(equality_resolution_simp,[status(thm)],[c_69542]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_12,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | ~ l1_pre_topc(X1)
% 19.30/2.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 19.30/2.99      inference(cnf_transformation,[],[f54]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_442,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 19.30/2.99      | sK0 != X1 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_443,plain,
% 19.30/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.30/2.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_442]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1061,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 19.30/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1320,plain,
% 19.30/2.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1065,c_1061]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3925,plain,
% 19.30/2.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1320,c_3819]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69543,plain,
% 19.30/2.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_69413,c_3925]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69548,plain,
% 19.30/2.99      ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_69547,c_69543]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_69549,plain,
% 19.30/2.99      ( $false ),
% 19.30/2.99      inference(equality_resolution_simp,[status(thm)],[c_69548]) ).
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.30/2.99  
% 19.30/2.99  ------                               Statistics
% 19.30/2.99  
% 19.30/2.99  ------ General
% 19.30/2.99  
% 19.30/2.99  abstr_ref_over_cycles:                  0
% 19.30/2.99  abstr_ref_under_cycles:                 0
% 19.30/2.99  gc_basic_clause_elim:                   0
% 19.30/2.99  forced_gc_time:                         0
% 19.30/2.99  parsing_time:                           0.009
% 19.30/2.99  unif_index_cands_time:                  0.
% 19.30/2.99  unif_index_add_time:                    0.
% 19.30/2.99  orderings_time:                         0.
% 19.30/2.99  out_proof_time:                         0.016
% 19.30/2.99  total_time:                             2.264
% 19.30/2.99  num_of_symbols:                         50
% 19.30/2.99  num_of_terms:                           76735
% 19.30/2.99  
% 19.30/2.99  ------ Preprocessing
% 19.30/2.99  
% 19.30/2.99  num_of_splits:                          4
% 19.30/2.99  num_of_split_atoms:                     2
% 19.30/2.99  num_of_reused_defs:                     2
% 19.30/2.99  num_eq_ax_congr_red:                    20
% 19.30/2.99  num_of_sem_filtered_clauses:            2
% 19.30/2.99  num_of_subtypes:                        0
% 19.30/2.99  monotx_restored_types:                  0
% 19.30/2.99  sat_num_of_epr_types:                   0
% 19.30/2.99  sat_num_of_non_cyclic_types:            0
% 19.30/2.99  sat_guarded_non_collapsed_types:        0
% 19.30/2.99  num_pure_diseq_elim:                    0
% 19.30/2.99  simp_replaced_by:                       0
% 19.30/2.99  res_preprocessed:                       98
% 19.30/2.99  prep_upred:                             0
% 19.30/2.99  prep_unflattend:                        16
% 19.30/2.99  smt_new_axioms:                         0
% 19.30/2.99  pred_elim_cands:                        1
% 19.30/2.99  pred_elim:                              4
% 19.30/2.99  pred_elim_cl:                           4
% 19.30/2.99  pred_elim_cycles:                       6
% 19.30/2.99  merged_defs:                            2
% 19.30/2.99  merged_defs_ncl:                        0
% 19.30/2.99  bin_hyper_res:                          2
% 19.30/2.99  prep_cycles:                            4
% 19.30/2.99  pred_elim_time:                         0.006
% 19.30/2.99  splitting_time:                         0.
% 19.30/2.99  sem_filter_time:                        0.
% 19.30/2.99  monotx_time:                            0.
% 19.30/2.99  subtype_inf_time:                       0.
% 19.30/2.99  
% 19.30/2.99  ------ Problem properties
% 19.30/2.99  
% 19.30/2.99  clauses:                                21
% 19.30/2.99  conjectures:                            1
% 19.30/2.99  epr:                                    1
% 19.30/2.99  horn:                                   19
% 19.30/2.99  ground:                                 4
% 19.30/2.99  unary:                                  3
% 19.30/2.99  binary:                                 13
% 19.30/2.99  lits:                                   45
% 19.30/2.99  lits_eq:                                14
% 19.30/2.99  fd_pure:                                0
% 19.30/2.99  fd_pseudo:                              0
% 19.30/2.99  fd_cond:                                0
% 19.30/2.99  fd_pseudo_cond:                         0
% 19.30/2.99  ac_symbols:                             0
% 19.30/2.99  
% 19.30/2.99  ------ Propositional Solver
% 19.30/2.99  
% 19.30/2.99  prop_solver_calls:                      35
% 19.30/2.99  prop_fast_solver_calls:                 1618
% 19.30/2.99  smt_solver_calls:                       0
% 19.30/2.99  smt_fast_solver_calls:                  0
% 19.30/2.99  prop_num_of_clauses:                    22192
% 19.30/2.99  prop_preprocess_simplified:             30477
% 19.30/2.99  prop_fo_subsumed:                       28
% 19.30/2.99  prop_solver_time:                       0.
% 19.30/2.99  smt_solver_time:                        0.
% 19.30/2.99  smt_fast_solver_time:                   0.
% 19.30/2.99  prop_fast_solver_time:                  0.
% 19.30/2.99  prop_unsat_core_time:                   0.
% 19.30/2.99  
% 19.30/2.99  ------ QBF
% 19.30/2.99  
% 19.30/2.99  qbf_q_res:                              0
% 19.30/2.99  qbf_num_tautologies:                    0
% 19.30/2.99  qbf_prep_cycles:                        0
% 19.30/2.99  
% 19.30/2.99  ------ BMC1
% 19.30/2.99  
% 19.30/2.99  bmc1_current_bound:                     -1
% 19.30/2.99  bmc1_last_solved_bound:                 -1
% 19.30/2.99  bmc1_unsat_core_size:                   -1
% 19.30/2.99  bmc1_unsat_core_parents_size:           -1
% 19.30/2.99  bmc1_merge_next_fun:                    0
% 19.30/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.30/2.99  
% 19.30/2.99  ------ Instantiation
% 19.30/2.99  
% 19.30/2.99  inst_num_of_clauses:                    5605
% 19.30/2.99  inst_num_in_passive:                    827
% 19.30/2.99  inst_num_in_active:                     2792
% 19.30/2.99  inst_num_in_unprocessed:                1986
% 19.30/2.99  inst_num_of_loops:                      2970
% 19.30/2.99  inst_num_of_learning_restarts:          0
% 19.30/2.99  inst_num_moves_active_passive:          176
% 19.30/2.99  inst_lit_activity:                      0
% 19.30/2.99  inst_lit_activity_moves:                4
% 19.30/2.99  inst_num_tautologies:                   0
% 19.30/2.99  inst_num_prop_implied:                  0
% 19.30/2.99  inst_num_existing_simplified:           0
% 19.30/2.99  inst_num_eq_res_simplified:             0
% 19.30/2.99  inst_num_child_elim:                    0
% 19.30/2.99  inst_num_of_dismatching_blockings:      29253
% 19.30/2.99  inst_num_of_non_proper_insts:           7235
% 19.30/2.99  inst_num_of_duplicates:                 0
% 19.30/2.99  inst_inst_num_from_inst_to_res:         0
% 19.30/2.99  inst_dismatching_checking_time:         0.
% 19.30/2.99  
% 19.30/2.99  ------ Resolution
% 19.30/2.99  
% 19.30/2.99  res_num_of_clauses:                     0
% 19.30/2.99  res_num_in_passive:                     0
% 19.30/2.99  res_num_in_active:                      0
% 19.30/2.99  res_num_of_loops:                       102
% 19.30/2.99  res_forward_subset_subsumed:            123
% 19.30/2.99  res_backward_subset_subsumed:           0
% 19.30/2.99  res_forward_subsumed:                   0
% 19.30/2.99  res_backward_subsumed:                  0
% 19.30/2.99  res_forward_subsumption_resolution:     0
% 19.30/2.99  res_backward_subsumption_resolution:    0
% 19.30/2.99  res_clause_to_clause_subsumption:       10389
% 19.30/2.99  res_orphan_elimination:                 0
% 19.30/2.99  res_tautology_del:                      300
% 19.30/2.99  res_num_eq_res_simplified:              1
% 19.30/2.99  res_num_sel_changes:                    0
% 19.30/2.99  res_moves_from_active_to_pass:          0
% 19.30/2.99  
% 19.30/2.99  ------ Superposition
% 19.30/2.99  
% 19.30/2.99  sup_time_total:                         0.
% 19.30/2.99  sup_time_generating:                    0.
% 19.30/2.99  sup_time_sim_full:                      0.
% 19.30/2.99  sup_time_sim_immed:                     0.
% 19.30/2.99  
% 19.30/2.99  sup_num_of_clauses:                     1923
% 19.30/2.99  sup_num_in_active:                      553
% 19.30/2.99  sup_num_in_passive:                     1370
% 19.30/2.99  sup_num_of_loops:                       592
% 19.30/2.99  sup_fw_superposition:                   3678
% 19.30/2.99  sup_bw_superposition:                   1543
% 19.30/2.99  sup_immediate_simplified:               2392
% 19.30/2.99  sup_given_eliminated:                   1
% 19.30/2.99  comparisons_done:                       0
% 19.30/2.99  comparisons_avoided:                    3
% 19.30/2.99  
% 19.30/2.99  ------ Simplifications
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  sim_fw_subset_subsumed:                 8
% 19.30/2.99  sim_bw_subset_subsumed:                 15
% 19.30/2.99  sim_fw_subsumed:                        261
% 19.30/2.99  sim_bw_subsumed:                        19
% 19.30/2.99  sim_fw_subsumption_res:                 0
% 19.30/2.99  sim_bw_subsumption_res:                 0
% 19.30/2.99  sim_tautology_del:                      1
% 19.30/2.99  sim_eq_tautology_del:                   1166
% 19.30/2.99  sim_eq_res_simp:                        1
% 19.30/2.99  sim_fw_demodulated:                     681
% 19.30/2.99  sim_bw_demodulated:                     35
% 19.30/2.99  sim_light_normalised:                   2009
% 19.30/2.99  sim_joinable_taut:                      0
% 19.30/2.99  sim_joinable_simp:                      0
% 19.30/2.99  sim_ac_normalised:                      0
% 19.30/2.99  sim_smt_subsumption:                    0
% 19.30/2.99  
%------------------------------------------------------------------------------
