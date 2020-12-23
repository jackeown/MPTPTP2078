%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1271+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:17 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 244 expanded)
%              Number of clauses        :   61 (  73 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  383 (1395 expanded)
%              Number of equality atoms :   59 (  60 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_tops_1(X2,X0)
                  & v3_tops_1(X1,X0) )
               => v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_tops_1(X2,X0)
                    & v3_tops_1(X1,X0) )
                 => v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_tops_1(X2,X0)
              & v3_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_tops_1(X2,X0)
              & v3_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v3_tops_1(X2,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v3_tops_1(sK2,X0)
        & v3_tops_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_tops_1(X2,X0)
              & v3_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v3_tops_1(X2,X0)
            & v3_tops_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_tops_1(X2,X0)
                & v3_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_tops_1(X2,sK0)
              & v3_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_tops_1(sK2,sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31,f30,f29])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v2_tops_1(X2,X0)
                  & v2_tops_1(X1,X0) )
               => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v2_tops_1(X2,X0)
              | ~ v2_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v2_tops_1(X2,X0)
              | ~ v2_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_tops_1(X2,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    v3_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_488,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_706,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_489,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_705,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)) = k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X0,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)) = k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X0,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_14])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1_41),k2_pre_topc(sK0,X0_41)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_248])).

cnf(c_708,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_41),k2_pre_topc(sK0,X1_41)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0_41,X1_41))
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_1424,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_41),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0_41,sK2))
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_708])).

cnf(c_1464,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_706,c_1424])).

cnf(c_5,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ v2_tops_1(X2,X1)
    | v2_tops_1(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_175,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ v2_tops_1(X2,X1)
    | v2_tops_1(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | X1 != X4
    | k2_pre_topc(X4,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_176,plain,
    ( ~ v2_tops_1(X0,X1)
    | v2_tops_1(k4_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_196,plain,
    ( ~ v2_tops_1(X0,X1)
    | v2_tops_1(k4_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_176,c_3])).

cnf(c_215,plain,
    ( ~ v2_tops_1(X0,X1)
    | v2_tops_1(k4_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_196,c_15])).

cnf(c_216,plain,
    ( ~ v2_tops_1(X0,sK0)
    | v2_tops_1(k4_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)),sK0)
    | ~ v2_tops_1(k2_pre_topc(sK0,X1),sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(k2_pre_topc(sK0,X1),sK0)
    | v2_tops_1(k4_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)),sK0)
    | ~ v2_tops_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_14])).

cnf(c_221,plain,
    ( ~ v2_tops_1(X0,sK0)
    | v2_tops_1(k4_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)),sK0)
    | ~ v2_tops_1(k2_pre_topc(sK0,X1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_487,plain,
    ( ~ v2_tops_1(X0_41,sK0)
    | v2_tops_1(k4_subset_1(u1_struct_0(sK0),X0_41,k2_pre_topc(sK0,X1_41)),sK0)
    | ~ v2_tops_1(k2_pre_topc(sK0,X1_41),sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_221])).

cnf(c_707,plain,
    ( v2_tops_1(X0_41,sK0) != iProver_top
    | v2_tops_1(k4_subset_1(u1_struct_0(sK0),X0_41,k2_pre_topc(sK0,X1_41)),sK0) = iProver_top
    | v2_tops_1(k2_pre_topc(sK0,X1_41),sK0) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_1657,plain,
    ( v2_tops_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) = iProver_top
    | v2_tops_1(k2_pre_topc(sK0,sK2),sK0) != iProver_top
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_707])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_42))
    | m1_subset_1(k4_subset_1(X0_42,X1_41,X0_41),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_813,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_814,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_816,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_316])).

cnf(c_522,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_524,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_11,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_273,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_14])).

cnf(c_274,plain,
    ( v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | ~ v3_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_377,plain,
    ( v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_274])).

cnf(c_378,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_379,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_10,negated_conjecture,
    ( v3_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_366,plain,
    ( v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_274])).

cnf(c_367,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_368,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK2),sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_9,negated_conjecture,
    ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
    | v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_288,plain,
    ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
    | v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_289,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | v3_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_356,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_289])).

cnf(c_357,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_358,plain,
    ( v2_tops_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) != iProver_top
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1657,c_816,c_524,c_379,c_368,c_358,c_19,c_18])).


%------------------------------------------------------------------------------
