%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:44 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 588 expanded)
%              Number of clauses        :   66 ( 171 expanded)
%              Number of leaves         :   11 ( 191 expanded)
%              Depth                    :   23
%              Number of atoms          :  337 (3654 expanded)
%              Number of equality atoms :  171 (1249 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v2_tops_2(X3,X1)
          & v2_tops_2(X2,X0)
          & X2 = X3
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ~ v2_tops_2(sK3,X1)
        & v2_tops_2(X2,X0)
        & sK3 = X2
        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,X1)
              & v2_tops_2(X2,X0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X3] :
            ( ~ v2_tops_2(X3,X1)
            & v2_tops_2(sK2,X0)
            & sK2 = X3
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,sK1)
                & v2_tops_2(X2,X0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X1)
                    & v2_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ v2_tops_2(sK3,sK1)
    & v2_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22,f21,f20,f19])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_413,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_424,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_420,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1178,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_420])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_40,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1179,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_420])).

cnf(c_1196,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1179])).

cnf(c_1200,plain,
    ( u1_struct_0(sK0) = X0
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1178,c_16,c_40,c_1196])).

cnf(c_1201,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(renaming,[status(thm)],[c_1200])).

cnf(c_1206,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_1201])).

cnf(c_8,plain,
    ( r1_tarski(X0,u1_pre_topc(X1))
    | ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_416,plain,
    ( r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
    | v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1314,plain,
    ( r1_tarski(X0,u1_pre_topc(sK0)) = iProver_top
    | v1_tops_2(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_416])).

cnf(c_17,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3378,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | v1_tops_2(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_pre_topc(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1314,c_17])).

cnf(c_3379,plain,
    ( r1_tarski(X0,u1_pre_topc(sK0)) = iProver_top
    | v1_tops_2(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3378])).

cnf(c_1310,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(demodulation,[status(thm)],[c_1206,c_12])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_421,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1679,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_421])).

cnf(c_422,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1313,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_422])).

cnf(c_1680,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK0) = X1
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_421])).

cnf(c_2650,plain,
    ( u1_pre_topc(sK0) = X1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1679,c_17,c_1313,c_1680])).

cnf(c_2651,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK0) = X1 ),
    inference(renaming,[status(thm)],[c_2650])).

cnf(c_2656,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
    inference(equality_resolution,[status(thm)],[c_2651])).

cnf(c_3384,plain,
    ( r1_tarski(X0,u1_pre_topc(sK1)) = iProver_top
    | v1_tops_2(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3379,c_2656])).

cnf(c_3391,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1)) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_3384])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_417,plain,
    ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
    | v1_tops_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1633,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_417])).

cnf(c_6482,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3391,c_1633])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7548,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK1) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6482,c_18])).

cnf(c_7549,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7548])).

cnf(c_7559,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK3),sK0) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_7549])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_423,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1015,plain,
    ( k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_413,c_423])).

cnf(c_6,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_418,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) = iProver_top
    | v1_tops_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1791,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),k7_setfam_1(u1_struct_0(X0),X1)),X0) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_418])).

cnf(c_5366,plain,
    ( v2_tops_2(sK3,sK1) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK3),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_1791])).

cnf(c_5,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
    | v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_419,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) != iProver_top
    | v1_tops_2(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1842,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X0),sK0) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_419])).

cnf(c_1847,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1842,c_1206])).

cnf(c_4194,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | v2_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1847,c_17])).

cnf(c_4195,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4194])).

cnf(c_4203,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),X0)),sK0) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_4195])).

cnf(c_5165,plain,
    ( v2_tops_2(sK3,sK0) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK3),sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_4203])).

cnf(c_10,negated_conjecture,
    ( v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_414,plain,
    ( v2_tops_2(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_431,plain,
    ( v2_tops_2(sK3,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_414,c_11])).

cnf(c_9,negated_conjecture,
    ( ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,plain,
    ( v2_tops_2(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7559,c_5366,c_5165,c_431,c_22,c_20,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:11:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.99  
% 3.62/0.99  ------  iProver source info
% 3.62/0.99  
% 3.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.99  git: non_committed_changes: false
% 3.62/0.99  git: last_make_outside_of_git: false
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  ------ Parsing...
% 3.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  ------ Proving...
% 3.62/0.99  ------ Problem Properties 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  clauses                                 17
% 3.62/0.99  conjectures                             8
% 3.62/0.99  EPR                                     5
% 3.62/0.99  Horn                                    17
% 3.62/0.99  unary                                   8
% 3.62/0.99  binary                                  3
% 3.62/0.99  lits                                    36
% 3.62/0.99  lits eq                                 7
% 3.62/0.99  fd_pure                                 0
% 3.62/0.99  fd_pseudo                               0
% 3.62/0.99  fd_cond                                 0
% 3.62/0.99  fd_pseudo_cond                          2
% 3.62/0.99  AC symbols                              0
% 3.62/0.99  
% 3.62/0.99  ------ Input Options Time Limit: Unbounded
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  Current options:
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS status Theorem for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  fof(f7,conjecture,(
% 3.62/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f8,negated_conjecture,(
% 3.62/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 3.62/0.99    inference(negated_conjecture,[],[f7])).
% 3.62/0.99  
% 3.62/0.99  fof(f15,plain,(
% 3.62/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tops_2(X3,X1) & (v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.62/0.99    inference(ennf_transformation,[],[f8])).
% 3.62/0.99  
% 3.62/0.99  fof(f16,plain,(
% 3.62/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.62/0.99    inference(flattening,[],[f15])).
% 3.62/0.99  
% 3.62/0.99  fof(f22,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) => (~v2_tops_2(sK3,X1) & v2_tops_2(X2,X0) & sK3 = X2 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f21,plain,(
% 3.62/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(sK2,X0) & sK2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f20,plain,(
% 3.62/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(sK1))) )),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f19,plain,(
% 3.62/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f23,plain,(
% 3.62/0.99    (((~v2_tops_2(sK3,sK1) & v2_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22,f21,f20,f19])).
% 3.62/0.99  
% 3.62/0.99  fof(f36,plain,(
% 3.62/0.99    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.62/0.99    inference(cnf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  fof(f1,axiom,(
% 3.62/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f9,plain,(
% 3.62/0.99    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.62/0.99    inference(ennf_transformation,[],[f1])).
% 3.62/0.99  
% 3.62/0.99  fof(f24,plain,(
% 3.62/0.99    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f9])).
% 3.62/0.99  
% 3.62/0.99  fof(f37,plain,(
% 3.62/0.99    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 3.62/0.99    inference(cnf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  fof(f4,axiom,(
% 3.62/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f12,plain,(
% 3.62/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.62/0.99    inference(ennf_transformation,[],[f4])).
% 3.62/0.99  
% 3.62/0.99  fof(f27,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f12])).
% 3.62/0.99  
% 3.62/0.99  fof(f33,plain,(
% 3.62/0.99    l1_pre_topc(sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  fof(f3,axiom,(
% 3.62/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f11,plain,(
% 3.62/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.99    inference(ennf_transformation,[],[f3])).
% 3.62/0.99  
% 3.62/0.99  fof(f26,plain,(
% 3.62/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f11])).
% 3.62/0.99  
% 3.62/0.99  fof(f6,axiom,(
% 3.62/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f14,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.62/0.99    inference(ennf_transformation,[],[f6])).
% 3.62/0.99  
% 3.62/0.99  fof(f18,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.62/0.99    inference(nnf_transformation,[],[f14])).
% 3.62/0.99  
% 3.62/0.99  fof(f31,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f28,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f12])).
% 3.62/0.99  
% 3.62/0.99  fof(f32,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f34,plain,(
% 3.62/0.99    l1_pre_topc(sK1)),
% 3.62/0.99    inference(cnf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  fof(f2,axiom,(
% 3.62/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f10,plain,(
% 3.62/0.99    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.62/0.99    inference(ennf_transformation,[],[f2])).
% 3.62/0.99  
% 3.62/0.99  fof(f25,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f10])).
% 3.62/0.99  
% 3.62/0.99  fof(f5,axiom,(
% 3.62/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f13,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.62/0.99    inference(ennf_transformation,[],[f5])).
% 3.62/0.99  
% 3.62/0.99  fof(f17,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.62/0.99    inference(nnf_transformation,[],[f13])).
% 3.62/0.99  
% 3.62/0.99  fof(f29,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f17])).
% 3.62/0.99  
% 3.62/0.99  fof(f30,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f17])).
% 3.62/0.99  
% 3.62/0.99  fof(f39,plain,(
% 3.62/0.99    v2_tops_2(sK2,sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  fof(f38,plain,(
% 3.62/0.99    sK2 = sK3),
% 3.62/0.99    inference(cnf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  fof(f40,plain,(
% 3.62/0.99    ~v2_tops_2(sK3,sK1)),
% 3.62/0.99    inference(cnf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  cnf(c_13,negated_conjecture,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_413,plain,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_0,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.62/0.99      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_424,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.62/0.99      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12,negated_conjecture,
% 3.62/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.62/0.99      | X2 = X1
% 3.62/0.99      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_420,plain,
% 3.62/0.99      ( X0 = X1
% 3.62/0.99      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.62/0.99      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1178,plain,
% 3.62/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.62/0.99      | u1_struct_0(sK0) = X0
% 3.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_12,c_420]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_16,negated_conjecture,
% 3.62/0.99      ( l1_pre_topc(sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2,plain,
% 3.62/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.62/0.99      | ~ l1_pre_topc(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_40,plain,
% 3.62/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.62/0.99      | ~ l1_pre_topc(sK0) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1179,plain,
% 3.62/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.62/0.99      | u1_struct_0(sK0) = X0
% 3.62/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_12,c_420]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1196,plain,
% 3.62/0.99      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.62/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.62/0.99      | u1_struct_0(sK0) = X0 ),
% 3.62/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1179]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1200,plain,
% 3.62/0.99      ( u1_struct_0(sK0) = X0
% 3.62/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_1178,c_16,c_40,c_1196]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1201,plain,
% 3.62/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.62/0.99      | u1_struct_0(sK0) = X0 ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_1200]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1206,plain,
% 3.62/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
% 3.62/0.99      inference(equality_resolution,[status(thm)],[c_1201]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_8,plain,
% 3.62/0.99      ( r1_tarski(X0,u1_pre_topc(X1))
% 3.62/0.99      | ~ v1_tops_2(X0,X1)
% 3.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.62/0.99      | ~ l1_pre_topc(X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_416,plain,
% 3.62/0.99      ( r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
% 3.62/0.99      | v1_tops_2(X0,X1) != iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1314,plain,
% 3.62/0.99      ( r1_tarski(X0,u1_pre_topc(sK0)) = iProver_top
% 3.62/0.99      | v1_tops_2(X0,sK0) != iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1206,c_416]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_17,plain,
% 3.62/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3378,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.62/0.99      | v1_tops_2(X0,sK0) != iProver_top
% 3.62/0.99      | r1_tarski(X0,u1_pre_topc(sK0)) = iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_1314,c_17]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3379,plain,
% 3.62/0.99      ( r1_tarski(X0,u1_pre_topc(sK0)) = iProver_top
% 3.62/0.99      | v1_tops_2(X0,sK0) != iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_3378]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1310,plain,
% 3.62/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_1206,c_12]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.62/0.99      | X2 = X0
% 3.62/0.99      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_421,plain,
% 3.62/0.99      ( X0 = X1
% 3.62/0.99      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 3.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1679,plain,
% 3.62/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.62/0.99      | u1_pre_topc(sK0) = X1
% 3.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1310,c_421]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_422,plain,
% 3.62/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.62/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1313,plain,
% 3.62/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.62/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1206,c_422]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1680,plain,
% 3.62/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.62/0.99      | u1_pre_topc(sK0) = X1
% 3.62/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1310,c_421]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2650,plain,
% 3.62/0.99      ( u1_pre_topc(sK0) = X1
% 3.62/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_1679,c_17,c_1313,c_1680]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2651,plain,
% 3.62/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.62/0.99      | u1_pre_topc(sK0) = X1 ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_2650]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2656,plain,
% 3.62/0.99      ( u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
% 3.62/0.99      inference(equality_resolution,[status(thm)],[c_2651]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3384,plain,
% 3.62/0.99      ( r1_tarski(X0,u1_pre_topc(sK1)) = iProver_top
% 3.62/0.99      | v1_tops_2(X0,sK0) != iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_3379,c_2656]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3391,plain,
% 3.62/0.99      ( r1_tarski(k7_setfam_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1)) = iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_424,c_3384]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.62/0.99      | v1_tops_2(X0,X1)
% 3.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.62/0.99      | ~ l1_pre_topc(X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_417,plain,
% 3.62/0.99      ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
% 3.62/0.99      | v1_tops_2(X0,X1) = iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1633,plain,
% 3.62/0.99      ( r1_tarski(k7_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) != iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_424,c_417]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6482,plain,
% 3.62/0.99      ( v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK1) = iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_3391,c_1633]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_15,negated_conjecture,
% 3.62/0.99      ( l1_pre_topc(sK1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_18,plain,
% 3.62/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7548,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK1) = iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_6482,c_18]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7549,plain,
% 3.62/0.99      ( v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK1) = iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_7548]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7559,plain,
% 3.62/0.99      ( v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK3),sK0) != iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK3),sK1) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_413,c_7549]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.62/0.99      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_423,plain,
% 3.62/0.99      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 3.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1015,plain,
% 3.62/0.99      ( k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),sK3)) = sK3 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_413,c_423]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6,plain,
% 3.62/0.99      ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
% 3.62/0.99      | ~ v1_tops_2(X1,X0)
% 3.62/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.62/0.99      | ~ l1_pre_topc(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_418,plain,
% 3.62/0.99      ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.62/0.99      | v1_tops_2(X1,X0) != iProver_top
% 3.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1791,plain,
% 3.62/0.99      ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),k7_setfam_1(u1_struct_0(X0),X1)),X0) = iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) != iProver_top
% 3.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_424,c_418]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5366,plain,
% 3.62/0.99      ( v2_tops_2(sK3,sK1) = iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK3),sK1) != iProver_top
% 3.62/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1015,c_1791]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5,plain,
% 3.62/0.99      ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
% 3.62/0.99      | v1_tops_2(X1,X0)
% 3.62/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.62/0.99      | ~ l1_pre_topc(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_419,plain,
% 3.62/0.99      ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) != iProver_top
% 3.62/0.99      | v1_tops_2(X1,X0) = iProver_top
% 3.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1842,plain,
% 3.62/0.99      ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X0),sK0) != iProver_top
% 3.62/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1206,c_419]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1847,plain,
% 3.62/0.99      ( v2_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
% 3.62/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.62/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_1842,c_1206]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4194,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.62/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 3.62/0.99      | v2_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_1847,c_17]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4195,plain,
% 3.62/0.99      ( v2_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) != iProver_top
% 3.62/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_4194]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4203,plain,
% 3.62/0.99      ( v2_tops_2(k7_setfam_1(u1_struct_0(sK1),k7_setfam_1(u1_struct_0(sK1),X0)),sK0) != iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),X0),sK0) = iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_424,c_4195]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5165,plain,
% 3.62/0.99      ( v2_tops_2(sK3,sK0) != iProver_top
% 3.62/0.99      | v1_tops_2(k7_setfam_1(u1_struct_0(sK1),sK3),sK0) = iProver_top
% 3.62/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1015,c_4203]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_10,negated_conjecture,
% 3.62/0.99      ( v2_tops_2(sK2,sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_414,plain,
% 3.62/0.99      ( v2_tops_2(sK2,sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_11,negated_conjecture,
% 3.62/0.99      ( sK2 = sK3 ),
% 3.62/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_431,plain,
% 3.62/0.99      ( v2_tops_2(sK3,sK0) = iProver_top ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_414,c_11]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_9,negated_conjecture,
% 3.62/0.99      ( ~ v2_tops_2(sK3,sK1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_22,plain,
% 3.62/0.99      ( v2_tops_2(sK3,sK1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_20,plain,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(contradiction,plain,
% 3.62/0.99      ( $false ),
% 3.62/0.99      inference(minisat,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_7559,c_5366,c_5165,c_431,c_22,c_20,c_18]) ).
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  ------                               Statistics
% 3.62/0.99  
% 3.62/0.99  ------ Selected
% 3.62/0.99  
% 3.62/0.99  total_time:                             0.249
% 3.62/0.99  
%------------------------------------------------------------------------------
