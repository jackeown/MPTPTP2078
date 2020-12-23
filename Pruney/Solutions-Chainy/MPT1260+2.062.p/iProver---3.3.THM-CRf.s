%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:23 EST 2020

% Result     : Theorem 15.90s
% Output     : CNFRefutation 15.90s
% Verified   : 
% Statistics : Number of formulae       :  153 (1724 expanded)
%              Number of clauses        :  102 ( 467 expanded)
%              Number of leaves         :   18 ( 446 expanded)
%              Depth                    :   27
%              Number of atoms          :  417 (6320 expanded)
%              Number of equality atoms :  202 (2349 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f30,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f49,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f37,f36,f36])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f36,f36])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_447,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1200,plain,
    ( X0 != X1
    | k4_xboole_0(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_447,c_4])).

cnf(c_3216,plain,
    ( X0 != X1
    | X2 != X0
    | k4_xboole_0(X1,k1_xboole_0) = X2 ),
    inference(resolution,[status(thm)],[c_1200,c_447])).

cnf(c_13,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_95,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_178,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_179,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_178])).

cnf(c_183,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_179,c_16])).

cnf(c_184,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_294,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_184])).

cnf(c_295,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_95,c_295])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_15])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_359])).

cnf(c_742,plain,
    ( ~ sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_442,c_15])).

cnf(c_14,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_97,plain,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_203,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_204,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_208,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_16])).

cnf(c_209,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_240,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_16])).

cnf(c_241,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_97,c_241])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_15])).

cnf(c_444,plain,
    ( sP0_iProver_split
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_338])).

cnf(c_747,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_742,c_444])).

cnf(c_44929,plain,
    ( k2_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,sK1) = sK1
    | k4_xboole_0(X0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[status(thm)],[c_3216,c_747])).

cnf(c_626,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_623,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_627,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6055,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_627])).

cnf(c_6857,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_626,c_6055])).

cnf(c_621,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_973,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_621,c_444,c_742])).

cnf(c_974,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_973])).

cnf(c_6874,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6857,c_974])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_638,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1,c_7])).

cnf(c_648,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),X2) ),
    inference(light_normalisation,[status(thm)],[c_5,c_638])).

cnf(c_649,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(demodulation,[status(thm)],[c_648,c_638])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_632,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_20005,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_649,c_632])).

cnf(c_1095,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_7])).

cnf(c_20030,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20005,c_1095])).

cnf(c_20002,plain,
    ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k4_xboole_0(X0,X2),X1))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_649,c_7])).

cnf(c_20502,plain,
    ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_632,c_20002])).

cnf(c_2136,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_638])).

cnf(c_2146,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2136,c_632])).

cnf(c_20634,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(k4_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(demodulation,[status(thm)],[c_20502,c_649,c_2146])).

cnf(c_20635,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_20634,c_4])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_641,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_638])).

cnf(c_22284,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_20635,c_641])).

cnf(c_2139,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_638,c_7])).

cnf(c_2356,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2139,c_641])).

cnf(c_22294,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_22284,c_1095,c_2356])).

cnf(c_34823,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20030,c_22294])).

cnf(c_34884,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_34823,c_641])).

cnf(c_10825,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2146,c_641])).

cnf(c_10832,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10825,c_4])).

cnf(c_34901,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_34884,c_10832])).

cnf(c_38021,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_6874,c_34901])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_625,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_760,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_626,c_625])).

cnf(c_6054,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_626,c_627])).

cnf(c_6554,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_760,c_6054])).

cnf(c_38178,plain,
    ( k1_tops_1(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_38021,c_6554])).

cnf(c_46766,plain,
    ( k1_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_44929,c_38178])).

cnf(c_446,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1208,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_447,c_446])).

cnf(c_46776,plain,
    ( sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_46766,c_1208])).

cnf(c_450,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_3139,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != k7_subset_1(X1,X3,X5)
    | k7_subset_1(X0,X2,X4) = X6 ),
    inference(resolution,[status(thm)],[c_450,c_447])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_3194,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ),
    inference(resolution,[status(thm)],[c_1208,c_271])).

cnf(c_13349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != k1_tops_1(sK0,X0)
    | X2 != k2_pre_topc(sK0,X0)
    | X3 != u1_struct_0(sK0)
    | k7_subset_1(X3,X2,X1) = k2_tops_1(sK0,X0) ),
    inference(resolution,[status(thm)],[c_3139,c_3194])).

cnf(c_443,plain,
    ( sP0_iProver_split
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_359])).

cnf(c_748,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_742,c_443])).

cnf(c_13976,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != sK1
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK1 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_13349,c_748])).

cnf(c_13977,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != sK1
    | sK1 != k1_tops_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_13976])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46776,c_38178,c_13977,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.90/2.58  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.90/2.58  
% 15.90/2.58  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.90/2.58  
% 15.90/2.58  ------  iProver source info
% 15.90/2.58  
% 15.90/2.58  git: date: 2020-06-30 10:37:57 +0100
% 15.90/2.58  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.90/2.58  git: non_committed_changes: false
% 15.90/2.58  git: last_make_outside_of_git: false
% 15.90/2.58  
% 15.90/2.58  ------ 
% 15.90/2.58  ------ Parsing...
% 15.90/2.58  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.90/2.58  
% 15.90/2.58  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 15.90/2.58  
% 15.90/2.58  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.90/2.58  
% 15.90/2.58  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.90/2.58  ------ Proving...
% 15.90/2.58  ------ Problem Properties 
% 15.90/2.58  
% 15.90/2.58  
% 15.90/2.58  clauses                                 16
% 15.90/2.58  conjectures                             1
% 15.90/2.58  EPR                                     0
% 15.90/2.58  Horn                                    15
% 15.90/2.58  unary                                   8
% 15.90/2.58  binary                                  6
% 15.90/2.58  lits                                    26
% 15.90/2.58  lits eq                                 14
% 15.90/2.58  fd_pure                                 0
% 15.90/2.58  fd_pseudo                               0
% 15.90/2.58  fd_cond                                 0
% 15.90/2.58  fd_pseudo_cond                          0
% 15.90/2.58  AC symbols                              0
% 15.90/2.58  
% 15.90/2.58  ------ Input Options Time Limit: Unbounded
% 15.90/2.58  
% 15.90/2.58  
% 15.90/2.58  ------ 
% 15.90/2.58  Current options:
% 15.90/2.58  ------ 
% 15.90/2.58  
% 15.90/2.58  
% 15.90/2.58  
% 15.90/2.58  
% 15.90/2.58  ------ Proving...
% 15.90/2.58  
% 15.90/2.58  
% 15.90/2.58  % SZS status Theorem for theBenchmark.p
% 15.90/2.58  
% 15.90/2.58  % SZS output start CNFRefutation for theBenchmark.p
% 15.90/2.58  
% 15.90/2.58  fof(f5,axiom,(
% 15.90/2.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f35,plain,(
% 15.90/2.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.90/2.58    inference(cnf_transformation,[],[f5])).
% 15.90/2.58  
% 15.90/2.58  fof(f14,conjecture,(
% 15.90/2.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f15,negated_conjecture,(
% 15.90/2.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 15.90/2.58    inference(negated_conjecture,[],[f14])).
% 15.90/2.58  
% 15.90/2.58  fof(f24,plain,(
% 15.90/2.58    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.90/2.58    inference(ennf_transformation,[],[f15])).
% 15.90/2.58  
% 15.90/2.58  fof(f25,plain,(
% 15.90/2.58    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.90/2.58    inference(flattening,[],[f24])).
% 15.90/2.58  
% 15.90/2.58  fof(f26,plain,(
% 15.90/2.58    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.90/2.58    inference(nnf_transformation,[],[f25])).
% 15.90/2.58  
% 15.90/2.58  fof(f27,plain,(
% 15.90/2.58    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.90/2.58    inference(flattening,[],[f26])).
% 15.90/2.58  
% 15.90/2.58  fof(f29,plain,(
% 15.90/2.58    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) != k2_tops_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) = k2_tops_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.90/2.58    introduced(choice_axiom,[])).
% 15.90/2.58  
% 15.90/2.58  fof(f28,plain,(
% 15.90/2.58    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) != k2_tops_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) = k2_tops_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 15.90/2.58    introduced(choice_axiom,[])).
% 15.90/2.58  
% 15.90/2.58  fof(f30,plain,(
% 15.90/2.58    ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 15.90/2.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 15.90/2.58  
% 15.90/2.58  fof(f49,plain,(
% 15.90/2.58    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 15.90/2.58    inference(cnf_transformation,[],[f30])).
% 15.90/2.58  
% 15.90/2.58  fof(f46,plain,(
% 15.90/2.58    l1_pre_topc(sK0)),
% 15.90/2.58    inference(cnf_transformation,[],[f30])).
% 15.90/2.58  
% 15.90/2.58  fof(f12,axiom,(
% 15.90/2.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f21,plain,(
% 15.90/2.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.90/2.58    inference(ennf_transformation,[],[f12])).
% 15.90/2.58  
% 15.90/2.58  fof(f22,plain,(
% 15.90/2.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.90/2.58    inference(flattening,[],[f21])).
% 15.90/2.58  
% 15.90/2.58  fof(f43,plain,(
% 15.90/2.58    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.90/2.58    inference(cnf_transformation,[],[f22])).
% 15.90/2.58  
% 15.90/2.58  fof(f45,plain,(
% 15.90/2.58    v2_pre_topc(sK0)),
% 15.90/2.58    inference(cnf_transformation,[],[f30])).
% 15.90/2.58  
% 15.90/2.58  fof(f47,plain,(
% 15.90/2.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.90/2.58    inference(cnf_transformation,[],[f30])).
% 15.90/2.58  
% 15.90/2.58  fof(f48,plain,(
% 15.90/2.58    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 15.90/2.58    inference(cnf_transformation,[],[f30])).
% 15.90/2.58  
% 15.90/2.58  fof(f42,plain,(
% 15.90/2.58    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.90/2.58    inference(cnf_transformation,[],[f22])).
% 15.90/2.58  
% 15.90/2.58  fof(f10,axiom,(
% 15.90/2.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f18,plain,(
% 15.90/2.58    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.90/2.58    inference(ennf_transformation,[],[f10])).
% 15.90/2.58  
% 15.90/2.58  fof(f19,plain,(
% 15.90/2.58    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.90/2.58    inference(flattening,[],[f18])).
% 15.90/2.58  
% 15.90/2.58  fof(f40,plain,(
% 15.90/2.58    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.90/2.58    inference(cnf_transformation,[],[f19])).
% 15.90/2.58  
% 15.90/2.58  fof(f8,axiom,(
% 15.90/2.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f17,plain,(
% 15.90/2.58    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.90/2.58    inference(ennf_transformation,[],[f8])).
% 15.90/2.58  
% 15.90/2.58  fof(f38,plain,(
% 15.90/2.58    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.90/2.58    inference(cnf_transformation,[],[f17])).
% 15.90/2.58  
% 15.90/2.58  fof(f7,axiom,(
% 15.90/2.58    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f37,plain,(
% 15.90/2.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.90/2.58    inference(cnf_transformation,[],[f7])).
% 15.90/2.58  
% 15.90/2.58  fof(f6,axiom,(
% 15.90/2.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f36,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.90/2.58    inference(cnf_transformation,[],[f6])).
% 15.90/2.58  
% 15.90/2.58  fof(f54,plain,(
% 15.90/2.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 15.90/2.58    inference(definition_unfolding,[],[f37,f36,f36])).
% 15.90/2.58  
% 15.90/2.58  fof(f1,axiom,(
% 15.90/2.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f31,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.90/2.58    inference(cnf_transformation,[],[f1])).
% 15.90/2.58  
% 15.90/2.58  fof(f51,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.90/2.58    inference(definition_unfolding,[],[f31,f36,f36])).
% 15.90/2.58  
% 15.90/2.58  fof(f9,axiom,(
% 15.90/2.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f39,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.90/2.58    inference(cnf_transformation,[],[f9])).
% 15.90/2.58  
% 15.90/2.58  fof(f55,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.90/2.58    inference(definition_unfolding,[],[f39,f36])).
% 15.90/2.58  
% 15.90/2.58  fof(f4,axiom,(
% 15.90/2.58    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f34,plain,(
% 15.90/2.58    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.90/2.58    inference(cnf_transformation,[],[f4])).
% 15.90/2.58  
% 15.90/2.58  fof(f53,plain,(
% 15.90/2.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 15.90/2.58    inference(definition_unfolding,[],[f34,f36])).
% 15.90/2.58  
% 15.90/2.58  fof(f3,axiom,(
% 15.90/2.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f33,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.90/2.58    inference(cnf_transformation,[],[f3])).
% 15.90/2.58  
% 15.90/2.58  fof(f50,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.90/2.58    inference(definition_unfolding,[],[f33,f36])).
% 15.90/2.58  
% 15.90/2.58  fof(f13,axiom,(
% 15.90/2.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f23,plain,(
% 15.90/2.58    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.90/2.58    inference(ennf_transformation,[],[f13])).
% 15.90/2.58  
% 15.90/2.58  fof(f44,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.90/2.58    inference(cnf_transformation,[],[f23])).
% 15.90/2.58  
% 15.90/2.58  fof(f11,axiom,(
% 15.90/2.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 15.90/2.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.90/2.58  
% 15.90/2.58  fof(f20,plain,(
% 15.90/2.58    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.90/2.58    inference(ennf_transformation,[],[f11])).
% 15.90/2.58  
% 15.90/2.58  fof(f41,plain,(
% 15.90/2.58    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.90/2.58    inference(cnf_transformation,[],[f20])).
% 15.90/2.58  
% 15.90/2.58  cnf(c_447,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_4,plain,
% 15.90/2.58      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.90/2.58      inference(cnf_transformation,[],[f35]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_1200,plain,
% 15.90/2.58      ( X0 != X1 | k4_xboole_0(X1,k1_xboole_0) = X0 ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_447,c_4]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_3216,plain,
% 15.90/2.58      ( X0 != X1 | X2 != X0 | k4_xboole_0(X1,k1_xboole_0) = X2 ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_1200,c_447]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_13,negated_conjecture,
% 15.90/2.58      ( ~ v3_pre_topc(sK1,sK0)
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(cnf_transformation,[],[f49]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_95,plain,
% 15.90/2.58      ( ~ v3_pre_topc(sK1,sK0)
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(prop_impl,[status(thm)],[c_13]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_16,negated_conjecture,
% 15.90/2.58      ( l1_pre_topc(sK0) ),
% 15.90/2.58      inference(cnf_transformation,[],[f46]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_10,plain,
% 15.90/2.58      ( v3_pre_topc(X0,X1)
% 15.90/2.58      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ v2_pre_topc(X1)
% 15.90/2.58      | ~ l1_pre_topc(X1)
% 15.90/2.58      | ~ l1_pre_topc(X3)
% 15.90/2.58      | k1_tops_1(X1,X0) != X0 ),
% 15.90/2.58      inference(cnf_transformation,[],[f43]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_17,negated_conjecture,
% 15.90/2.58      ( v2_pre_topc(sK0) ),
% 15.90/2.58      inference(cnf_transformation,[],[f45]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_178,plain,
% 15.90/2.58      ( v3_pre_topc(X0,X1)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 15.90/2.58      | ~ l1_pre_topc(X1)
% 15.90/2.58      | ~ l1_pre_topc(X3)
% 15.90/2.58      | k1_tops_1(X1,X0) != X0
% 15.90/2.58      | sK0 != X1 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_179,plain,
% 15.90/2.58      ( v3_pre_topc(X0,sK0)
% 15.90/2.58      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ l1_pre_topc(X2)
% 15.90/2.58      | ~ l1_pre_topc(sK0)
% 15.90/2.58      | k1_tops_1(sK0,X0) != X0 ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_178]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_183,plain,
% 15.90/2.58      ( ~ l1_pre_topc(X2)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 15.90/2.58      | v3_pre_topc(X0,sK0)
% 15.90/2.58      | k1_tops_1(sK0,X0) != X0 ),
% 15.90/2.58      inference(global_propositional_subsumption,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_179,c_16]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_184,plain,
% 15.90/2.58      ( v3_pre_topc(X0,sK0)
% 15.90/2.58      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ l1_pre_topc(X2)
% 15.90/2.58      | k1_tops_1(sK0,X0) != X0 ),
% 15.90/2.58      inference(renaming,[status(thm)],[c_183]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_294,plain,
% 15.90/2.58      ( v3_pre_topc(X0,sK0)
% 15.90/2.58      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k1_tops_1(sK0,X0) != X0
% 15.90/2.58      | sK0 != X2 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_16,c_184]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_295,plain,
% 15.90/2.58      ( v3_pre_topc(X0,sK0)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k1_tops_1(sK0,X0) != X0 ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_294]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_354,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,X0) != X0
% 15.90/2.58      | sK1 != X0
% 15.90/2.58      | sK0 != sK0 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_95,c_295]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_355,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) != sK1 ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_354]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_15,negated_conjecture,
% 15.90/2.58      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.90/2.58      inference(cnf_transformation,[],[f47]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_359,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) != sK1 ),
% 15.90/2.58      inference(global_propositional_subsumption,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_355,c_15]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_442,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ sP0_iProver_split ),
% 15.90/2.58      inference(splitting,
% 15.90/2.58                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 15.90/2.58                [c_359]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_742,plain,
% 15.90/2.58      ( ~ sP0_iProver_split ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_442,c_15]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_14,negated_conjecture,
% 15.90/2.58      ( v3_pre_topc(sK1,sK0)
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(cnf_transformation,[],[f48]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_97,plain,
% 15.90/2.58      ( v3_pre_topc(sK1,sK0)
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(prop_impl,[status(thm)],[c_14]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_11,plain,
% 15.90/2.58      ( ~ v3_pre_topc(X0,X1)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 15.90/2.58      | ~ v2_pre_topc(X3)
% 15.90/2.58      | ~ l1_pre_topc(X3)
% 15.90/2.58      | ~ l1_pre_topc(X1)
% 15.90/2.58      | k1_tops_1(X1,X0) = X0 ),
% 15.90/2.58      inference(cnf_transformation,[],[f42]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_203,plain,
% 15.90/2.58      ( ~ v3_pre_topc(X0,X1)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 15.90/2.58      | ~ l1_pre_topc(X1)
% 15.90/2.58      | ~ l1_pre_topc(X3)
% 15.90/2.58      | k1_tops_1(X1,X0) = X0
% 15.90/2.58      | sK0 != X3 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_204,plain,
% 15.90/2.58      ( ~ v3_pre_topc(X0,X1)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ l1_pre_topc(X1)
% 15.90/2.58      | ~ l1_pre_topc(sK0)
% 15.90/2.58      | k1_tops_1(X1,X0) = X0 ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_203]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_208,plain,
% 15.90/2.58      ( ~ l1_pre_topc(X1)
% 15.90/2.58      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ v3_pre_topc(X0,X1)
% 15.90/2.58      | k1_tops_1(X1,X0) = X0 ),
% 15.90/2.58      inference(global_propositional_subsumption,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_204,c_16]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_209,plain,
% 15.90/2.58      ( ~ v3_pre_topc(X0,X1)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ l1_pre_topc(X1)
% 15.90/2.58      | k1_tops_1(X1,X0) = X0 ),
% 15.90/2.58      inference(renaming,[status(thm)],[c_208]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_240,plain,
% 15.90/2.58      ( ~ v3_pre_topc(X0,X1)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k1_tops_1(X1,X0) = X0
% 15.90/2.58      | sK0 != X1 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_209,c_16]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_241,plain,
% 15.90/2.58      ( ~ v3_pre_topc(X0,sK0)
% 15.90/2.58      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k1_tops_1(sK0,X0) = X0 ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_240]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_333,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,X0) = X0
% 15.90/2.58      | sK1 != X0
% 15.90/2.58      | sK0 != sK0 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_97,c_241]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_334,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) = sK1 ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_333]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_338,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) = sK1 ),
% 15.90/2.58      inference(global_propositional_subsumption,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_334,c_15]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_444,plain,
% 15.90/2.58      ( sP0_iProver_split
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) = sK1 ),
% 15.90/2.58      inference(splitting,
% 15.90/2.58                [splitting(split),new_symbols(definition,[])],
% 15.90/2.58                [c_338]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_747,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) = sK1 ),
% 15.90/2.58      inference(backward_subsumption_resolution,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_742,c_444]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_44929,plain,
% 15.90/2.58      ( k2_tops_1(sK0,sK1) != X0
% 15.90/2.58      | k1_tops_1(sK0,sK1) = sK1
% 15.90/2.58      | k4_xboole_0(X0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_3216,c_747]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_626,plain,
% 15.90/2.58      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.90/2.58      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_8,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ l1_pre_topc(X1) ),
% 15.90/2.58      inference(cnf_transformation,[],[f40]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_282,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | sK0 != X1 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_283,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_282]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_623,plain,
% 15.90/2.58      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.90/2.58      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.90/2.58      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_6,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.90/2.58      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 15.90/2.58      inference(cnf_transformation,[],[f38]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_627,plain,
% 15.90/2.58      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 15.90/2.58      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.90/2.58      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_6055,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
% 15.90/2.58      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_623,c_627]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_6857,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_626,c_6055]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_621,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) = sK1
% 15.90/2.58      | sP0_iProver_split = iProver_top ),
% 15.90/2.58      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_973,plain,
% 15.90/2.58      ( k1_tops_1(sK0,sK1) = sK1
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(global_propositional_subsumption,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_621,c_444,c_742]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_974,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) = sK1 ),
% 15.90/2.58      inference(renaming,[status(thm)],[c_973]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_6874,plain,
% 15.90/2.58      ( k1_tops_1(sK0,sK1) = sK1
% 15.90/2.58      | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_6857,c_974]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_5,plain,
% 15.90/2.58      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 15.90/2.58      inference(cnf_transformation,[],[f54]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_1,plain,
% 15.90/2.58      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.90/2.58      inference(cnf_transformation,[],[f51]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_7,plain,
% 15.90/2.58      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 15.90/2.58      inference(cnf_transformation,[],[f55]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_638,plain,
% 15.90/2.58      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_1,c_7]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_648,plain,
% 15.90/2.58      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),X2) ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_5,c_638]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_649,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 15.90/2.58      inference(demodulation,[status(thm)],[c_648,c_638]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_3,plain,
% 15.90/2.58      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.90/2.58      inference(cnf_transformation,[],[f53]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_632,plain,
% 15.90/2.58      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_20005,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1)) = k1_xboole_0 ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_649,c_632]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_1095,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_7,c_7]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_20030,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))),X1)) = k1_xboole_0 ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_20005,c_1095]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_20002,plain,
% 15.90/2.58      ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k4_xboole_0(X0,X2),X1))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_649,c_7]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_20502,plain,
% 15.90/2.58      ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_632,c_20002]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_2136,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_4,c_638]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_2146,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_2136,c_632]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_20634,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(k4_xboole_0(X0,k1_xboole_0),X1)) ),
% 15.90/2.58      inference(demodulation,[status(thm)],[c_20502,c_649,c_2146]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_20635,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_20634,c_4]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_0,plain,
% 15.90/2.58      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.90/2.58      inference(cnf_transformation,[],[f50]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_641,plain,
% 15.90/2.58      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_0,c_638]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_22284,plain,
% 15.90/2.58      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_20635,c_641]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_2139,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_638,c_7]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_2356,plain,
% 15.90/2.58      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_2139,c_641]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_22294,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.90/2.58      inference(light_normalisation,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_22284,c_1095,c_2356]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_34823,plain,
% 15.90/2.58      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_20030,c_22294]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_34884,plain,
% 15.90/2.58      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_34823,c_641]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_10825,plain,
% 15.90/2.58      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_2146,c_641]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_10832,plain,
% 15.90/2.58      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_10825,c_4]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_34901,plain,
% 15.90/2.58      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 15.90/2.58      inference(light_normalisation,[status(thm)],[c_34884,c_10832]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_38021,plain,
% 15.90/2.58      ( k1_tops_1(sK0,sK1) = sK1
% 15.90/2.58      | k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_6874,c_34901]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_12,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ l1_pre_topc(X1)
% 15.90/2.58      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 15.90/2.58      inference(cnf_transformation,[],[f44]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_258,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 15.90/2.58      | sK0 != X1 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_259,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_258]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_625,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 15.90/2.58      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.90/2.58      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_760,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_626,c_625]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_6054,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_626,c_627]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_6554,plain,
% 15.90/2.58      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(superposition,[status(thm)],[c_760,c_6054]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_38178,plain,
% 15.90/2.58      ( k1_tops_1(sK0,sK1) = sK1 ),
% 15.90/2.58      inference(demodulation,[status(thm)],[c_38021,c_6554]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_46766,plain,
% 15.90/2.58      ( k1_tops_1(sK0,sK1) = sK1 ),
% 15.90/2.58      inference(global_propositional_subsumption,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_44929,c_38178]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_446,plain,( X0 = X0 ),theory(equality) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_1208,plain,
% 15.90/2.58      ( X0 != X1 | X1 = X0 ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_447,c_446]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_46776,plain,
% 15.90/2.58      ( sK1 = k1_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_46766,c_1208]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_450,plain,
% 15.90/2.58      ( X0 != X1
% 15.90/2.58      | X2 != X3
% 15.90/2.58      | X4 != X5
% 15.90/2.58      | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
% 15.90/2.58      theory(equality) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_3139,plain,
% 15.90/2.58      ( X0 != X1
% 15.90/2.58      | X2 != X3
% 15.90/2.58      | X4 != X5
% 15.90/2.58      | X6 != k7_subset_1(X1,X3,X5)
% 15.90/2.58      | k7_subset_1(X0,X2,X4) = X6 ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_450,c_447]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_9,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | ~ l1_pre_topc(X1)
% 15.90/2.58      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 15.90/2.58      inference(cnf_transformation,[],[f41]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_270,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 15.90/2.58      | sK0 != X1 ),
% 15.90/2.58      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_271,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 15.90/2.58      inference(unflattening,[status(thm)],[c_270]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_3194,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_1208,c_271]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_13349,plain,
% 15.90/2.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | X1 != k1_tops_1(sK0,X0)
% 15.90/2.58      | X2 != k2_pre_topc(sK0,X0)
% 15.90/2.58      | X3 != u1_struct_0(sK0)
% 15.90/2.58      | k7_subset_1(X3,X2,X1) = k2_tops_1(sK0,X0) ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_3139,c_3194]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_443,plain,
% 15.90/2.58      ( sP0_iProver_split
% 15.90/2.58      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) != sK1 ),
% 15.90/2.58      inference(splitting,
% 15.90/2.58                [splitting(split),new_symbols(definition,[])],
% 15.90/2.58                [c_359]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_748,plain,
% 15.90/2.58      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 15.90/2.58      | k1_tops_1(sK0,sK1) != sK1 ),
% 15.90/2.58      inference(backward_subsumption_resolution,
% 15.90/2.58                [status(thm)],
% 15.90/2.58                [c_742,c_443]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_13976,plain,
% 15.90/2.58      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k1_tops_1(sK0,sK1) != sK1
% 15.90/2.58      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1)
% 15.90/2.58      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 15.90/2.58      | sK1 != k1_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(resolution,[status(thm)],[c_13349,c_748]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(c_13977,plain,
% 15.90/2.58      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.90/2.58      | k1_tops_1(sK0,sK1) != sK1
% 15.90/2.58      | sK1 != k1_tops_1(sK0,sK1) ),
% 15.90/2.58      inference(equality_resolution_simp,[status(thm)],[c_13976]) ).
% 15.90/2.58  
% 15.90/2.58  cnf(contradiction,plain,
% 15.90/2.58      ( $false ),
% 15.90/2.58      inference(minisat,[status(thm)],[c_46776,c_38178,c_13977,c_15]) ).
% 15.90/2.58  
% 15.90/2.58  
% 15.90/2.58  % SZS output end CNFRefutation for theBenchmark.p
% 15.90/2.58  
% 15.90/2.58  ------                               Statistics
% 15.90/2.58  
% 15.90/2.58  ------ Selected
% 15.90/2.58  
% 15.90/2.58  total_time:                             1.986
% 15.90/2.58  
%------------------------------------------------------------------------------
