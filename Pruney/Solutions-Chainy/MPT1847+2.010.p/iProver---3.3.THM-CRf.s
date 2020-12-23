%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:25 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 770 expanded)
%              Number of clauses        :   83 ( 238 expanded)
%              Number of leaves         :   15 ( 216 expanded)
%              Depth                    :   21
%              Number of atoms          :  439 (3778 expanded)
%              Number of equality atoms :  195 ( 881 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tex_2(X2,X0)
          & v1_tex_2(X1,X0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_pre_topc(X2,X0) )
     => ( ~ v1_tex_2(sK3,X0)
        & v1_tex_2(X1,X0)
        & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ v1_tex_2(X2,X0)
            & v1_tex_2(sK2,X0)
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK1)
              & v1_tex_2(X1,sK1)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK1) )
          & m1_pre_topc(X1,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ v1_tex_2(sK3,sK1)
    & v1_tex_2(sK2,sK1)
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & m1_pre_topc(sK3,sK1)
    & m1_pre_topc(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f28,f27,f26])).

fof(f46,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ~ v1_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1061,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_103,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_3])).

cnf(c_104,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_103])).

cnf(c_1050,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_1315,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1050])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1052,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1063,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1326,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1052,c_1063])).

cnf(c_1522,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1315,c_19,c_1326])).

cnf(c_1523,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1522])).

cnf(c_4,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1062,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1531,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1062])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1053,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1325,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1063])).

cnf(c_1715,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1531,c_19,c_1325])).

cnf(c_1716,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_1715])).

cnf(c_1723,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_1716])).

cnf(c_2233,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_19,c_1326])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1060,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1065,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1395,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_1065])).

cnf(c_2586,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_1395])).

cnf(c_47,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3553,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2586,c_47])).

cnf(c_3554,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3553])).

cnf(c_3569,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_3554])).

cnf(c_1502,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1062])).

cnf(c_1612,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1502,c_19,c_1326])).

cnf(c_1613,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_1612])).

cnf(c_1620,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_1613])).

cnf(c_1794,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1620,c_19,c_1325])).

cnf(c_1795,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_1794])).

cnf(c_1802,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_1795])).

cnf(c_4384,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3569,c_19,c_1325,c_1802])).

cnf(c_12,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1056,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | v1_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4425,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | v1_tex_2(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4384,c_1056])).

cnf(c_4481,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | v1_tex_2(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4425,c_4384])).

cnf(c_4564,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4481])).

cnf(c_10,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1058,plain,
    ( sK0(X0,X1) = u1_struct_0(X1)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1976,plain,
    ( sK0(sK1,sK3) = u1_struct_0(sK3)
    | v1_tex_2(sK3,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1058])).

cnf(c_13,negated_conjecture,
    ( ~ v1_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_357,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_358,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_2127,plain,
    ( sK0(sK1,sK3) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1976,c_18,c_16,c_358])).

cnf(c_9,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1059,plain,
    ( v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) != iProver_top
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2130,plain,
    ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(sK3,sK1) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_1059])).

cnf(c_722,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1582,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1211,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != sK0(sK1,sK3)
    | X1 != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1360,plain,
    ( ~ m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(u1_struct_0(sK3),X0)
    | X0 != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK3) != sK0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_1567,plain,
    ( ~ m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK3) != sK0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_1569,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK3) != sK0(sK1,sK3)
    | m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_1571,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK3) != sK0(sK1,sK3)
    | m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1569])).

cnf(c_1350,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_723,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1256,plain,
    ( X0 != X1
    | X0 = sK0(sK1,sK3)
    | sK0(sK1,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1297,plain,
    ( X0 = sK0(sK1,sK3)
    | X0 != u1_struct_0(sK3)
    | sK0(sK1,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_1349,plain,
    ( sK0(sK1,sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK0(sK1,sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_11,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_335,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_336,plain,
    ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_337,plain,
    ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_23,plain,
    ( v1_tex_2(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,plain,
    ( v1_tex_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_21,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4564,c_2130,c_1582,c_1571,c_1350,c_1349,c_358,c_337,c_23,c_22,c_21,c_16,c_20,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:23:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.22/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/1.02  
% 2.22/1.02  ------  iProver source info
% 2.22/1.02  
% 2.22/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.22/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/1.02  git: non_committed_changes: false
% 2.22/1.02  git: last_make_outside_of_git: false
% 2.22/1.02  
% 2.22/1.02  ------ 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options
% 2.22/1.02  
% 2.22/1.02  --out_options                           all
% 2.22/1.02  --tptp_safe_out                         true
% 2.22/1.02  --problem_path                          ""
% 2.22/1.02  --include_path                          ""
% 2.22/1.02  --clausifier                            res/vclausify_rel
% 2.22/1.02  --clausifier_options                    --mode clausify
% 2.22/1.02  --stdin                                 false
% 2.22/1.02  --stats_out                             all
% 2.22/1.02  
% 2.22/1.02  ------ General Options
% 2.22/1.02  
% 2.22/1.02  --fof                                   false
% 2.22/1.02  --time_out_real                         305.
% 2.22/1.02  --time_out_virtual                      -1.
% 2.22/1.02  --symbol_type_check                     false
% 2.22/1.02  --clausify_out                          false
% 2.22/1.02  --sig_cnt_out                           false
% 2.22/1.02  --trig_cnt_out                          false
% 2.22/1.02  --trig_cnt_out_tolerance                1.
% 2.22/1.02  --trig_cnt_out_sk_spl                   false
% 2.22/1.02  --abstr_cl_out                          false
% 2.22/1.02  
% 2.22/1.02  ------ Global Options
% 2.22/1.02  
% 2.22/1.02  --schedule                              default
% 2.22/1.02  --add_important_lit                     false
% 2.22/1.02  --prop_solver_per_cl                    1000
% 2.22/1.02  --min_unsat_core                        false
% 2.22/1.02  --soft_assumptions                      false
% 2.22/1.02  --soft_lemma_size                       3
% 2.22/1.02  --prop_impl_unit_size                   0
% 2.22/1.02  --prop_impl_unit                        []
% 2.22/1.02  --share_sel_clauses                     true
% 2.22/1.02  --reset_solvers                         false
% 2.22/1.02  --bc_imp_inh                            [conj_cone]
% 2.22/1.02  --conj_cone_tolerance                   3.
% 2.22/1.02  --extra_neg_conj                        none
% 2.22/1.02  --large_theory_mode                     true
% 2.22/1.02  --prolific_symb_bound                   200
% 2.22/1.02  --lt_threshold                          2000
% 2.22/1.02  --clause_weak_htbl                      true
% 2.22/1.02  --gc_record_bc_elim                     false
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing Options
% 2.22/1.02  
% 2.22/1.02  --preprocessing_flag                    true
% 2.22/1.02  --time_out_prep_mult                    0.1
% 2.22/1.02  --splitting_mode                        input
% 2.22/1.02  --splitting_grd                         true
% 2.22/1.02  --splitting_cvd                         false
% 2.22/1.02  --splitting_cvd_svl                     false
% 2.22/1.02  --splitting_nvd                         32
% 2.22/1.02  --sub_typing                            true
% 2.22/1.02  --prep_gs_sim                           true
% 2.22/1.02  --prep_unflatten                        true
% 2.22/1.02  --prep_res_sim                          true
% 2.22/1.02  --prep_upred                            true
% 2.22/1.02  --prep_sem_filter                       exhaustive
% 2.22/1.02  --prep_sem_filter_out                   false
% 2.22/1.02  --pred_elim                             true
% 2.22/1.02  --res_sim_input                         true
% 2.22/1.02  --eq_ax_congr_red                       true
% 2.22/1.02  --pure_diseq_elim                       true
% 2.22/1.02  --brand_transform                       false
% 2.22/1.02  --non_eq_to_eq                          false
% 2.22/1.02  --prep_def_merge                        true
% 2.22/1.02  --prep_def_merge_prop_impl              false
% 2.22/1.02  --prep_def_merge_mbd                    true
% 2.22/1.02  --prep_def_merge_tr_red                 false
% 2.22/1.02  --prep_def_merge_tr_cl                  false
% 2.22/1.02  --smt_preprocessing                     true
% 2.22/1.02  --smt_ac_axioms                         fast
% 2.22/1.02  --preprocessed_out                      false
% 2.22/1.02  --preprocessed_stats                    false
% 2.22/1.02  
% 2.22/1.02  ------ Abstraction refinement Options
% 2.22/1.02  
% 2.22/1.02  --abstr_ref                             []
% 2.22/1.02  --abstr_ref_prep                        false
% 2.22/1.02  --abstr_ref_until_sat                   false
% 2.22/1.02  --abstr_ref_sig_restrict                funpre
% 2.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.02  --abstr_ref_under                       []
% 2.22/1.02  
% 2.22/1.02  ------ SAT Options
% 2.22/1.02  
% 2.22/1.02  --sat_mode                              false
% 2.22/1.02  --sat_fm_restart_options                ""
% 2.22/1.02  --sat_gr_def                            false
% 2.22/1.02  --sat_epr_types                         true
% 2.22/1.02  --sat_non_cyclic_types                  false
% 2.22/1.02  --sat_finite_models                     false
% 2.22/1.02  --sat_fm_lemmas                         false
% 2.22/1.02  --sat_fm_prep                           false
% 2.22/1.02  --sat_fm_uc_incr                        true
% 2.22/1.02  --sat_out_model                         small
% 2.22/1.02  --sat_out_clauses                       false
% 2.22/1.02  
% 2.22/1.02  ------ QBF Options
% 2.22/1.02  
% 2.22/1.02  --qbf_mode                              false
% 2.22/1.02  --qbf_elim_univ                         false
% 2.22/1.02  --qbf_dom_inst                          none
% 2.22/1.02  --qbf_dom_pre_inst                      false
% 2.22/1.02  --qbf_sk_in                             false
% 2.22/1.02  --qbf_pred_elim                         true
% 2.22/1.02  --qbf_split                             512
% 2.22/1.02  
% 2.22/1.02  ------ BMC1 Options
% 2.22/1.02  
% 2.22/1.02  --bmc1_incremental                      false
% 2.22/1.02  --bmc1_axioms                           reachable_all
% 2.22/1.02  --bmc1_min_bound                        0
% 2.22/1.02  --bmc1_max_bound                        -1
% 2.22/1.02  --bmc1_max_bound_default                -1
% 2.22/1.02  --bmc1_symbol_reachability              true
% 2.22/1.02  --bmc1_property_lemmas                  false
% 2.22/1.02  --bmc1_k_induction                      false
% 2.22/1.02  --bmc1_non_equiv_states                 false
% 2.22/1.02  --bmc1_deadlock                         false
% 2.22/1.02  --bmc1_ucm                              false
% 2.22/1.02  --bmc1_add_unsat_core                   none
% 2.22/1.02  --bmc1_unsat_core_children              false
% 2.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.02  --bmc1_out_stat                         full
% 2.22/1.02  --bmc1_ground_init                      false
% 2.22/1.02  --bmc1_pre_inst_next_state              false
% 2.22/1.02  --bmc1_pre_inst_state                   false
% 2.22/1.02  --bmc1_pre_inst_reach_state             false
% 2.22/1.02  --bmc1_out_unsat_core                   false
% 2.22/1.02  --bmc1_aig_witness_out                  false
% 2.22/1.02  --bmc1_verbose                          false
% 2.22/1.02  --bmc1_dump_clauses_tptp                false
% 2.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.02  --bmc1_dump_file                        -
% 2.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.02  --bmc1_ucm_extend_mode                  1
% 2.22/1.02  --bmc1_ucm_init_mode                    2
% 2.22/1.02  --bmc1_ucm_cone_mode                    none
% 2.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.02  --bmc1_ucm_relax_model                  4
% 2.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.02  --bmc1_ucm_layered_model                none
% 2.22/1.02  --bmc1_ucm_max_lemma_size               10
% 2.22/1.02  
% 2.22/1.02  ------ AIG Options
% 2.22/1.02  
% 2.22/1.02  --aig_mode                              false
% 2.22/1.02  
% 2.22/1.02  ------ Instantiation Options
% 2.22/1.02  
% 2.22/1.02  --instantiation_flag                    true
% 2.22/1.02  --inst_sos_flag                         false
% 2.22/1.02  --inst_sos_phase                        true
% 2.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel_side                     num_symb
% 2.22/1.02  --inst_solver_per_active                1400
% 2.22/1.02  --inst_solver_calls_frac                1.
% 2.22/1.02  --inst_passive_queue_type               priority_queues
% 2.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.02  --inst_passive_queues_freq              [25;2]
% 2.22/1.02  --inst_dismatching                      true
% 2.22/1.02  --inst_eager_unprocessed_to_passive     true
% 2.22/1.02  --inst_prop_sim_given                   true
% 2.22/1.02  --inst_prop_sim_new                     false
% 2.22/1.02  --inst_subs_new                         false
% 2.22/1.02  --inst_eq_res_simp                      false
% 2.22/1.02  --inst_subs_given                       false
% 2.22/1.02  --inst_orphan_elimination               true
% 2.22/1.02  --inst_learning_loop_flag               true
% 2.22/1.02  --inst_learning_start                   3000
% 2.22/1.02  --inst_learning_factor                  2
% 2.22/1.02  --inst_start_prop_sim_after_learn       3
% 2.22/1.02  --inst_sel_renew                        solver
% 2.22/1.02  --inst_lit_activity_flag                true
% 2.22/1.02  --inst_restr_to_given                   false
% 2.22/1.02  --inst_activity_threshold               500
% 2.22/1.02  --inst_out_proof                        true
% 2.22/1.02  
% 2.22/1.02  ------ Resolution Options
% 2.22/1.02  
% 2.22/1.02  --resolution_flag                       true
% 2.22/1.02  --res_lit_sel                           adaptive
% 2.22/1.02  --res_lit_sel_side                      none
% 2.22/1.02  --res_ordering                          kbo
% 2.22/1.02  --res_to_prop_solver                    active
% 2.22/1.02  --res_prop_simpl_new                    false
% 2.22/1.02  --res_prop_simpl_given                  true
% 2.22/1.02  --res_passive_queue_type                priority_queues
% 2.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.02  --res_passive_queues_freq               [15;5]
% 2.22/1.02  --res_forward_subs                      full
% 2.22/1.02  --res_backward_subs                     full
% 2.22/1.02  --res_forward_subs_resolution           true
% 2.22/1.02  --res_backward_subs_resolution          true
% 2.22/1.02  --res_orphan_elimination                true
% 2.22/1.02  --res_time_limit                        2.
% 2.22/1.02  --res_out_proof                         true
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Options
% 2.22/1.02  
% 2.22/1.02  --superposition_flag                    true
% 2.22/1.02  --sup_passive_queue_type                priority_queues
% 2.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.02  --demod_completeness_check              fast
% 2.22/1.02  --demod_use_ground                      true
% 2.22/1.02  --sup_to_prop_solver                    passive
% 2.22/1.02  --sup_prop_simpl_new                    true
% 2.22/1.02  --sup_prop_simpl_given                  true
% 2.22/1.02  --sup_fun_splitting                     false
% 2.22/1.02  --sup_smt_interval                      50000
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Simplification Setup
% 2.22/1.02  
% 2.22/1.02  --sup_indices_passive                   []
% 2.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_full_bw                           [BwDemod]
% 2.22/1.02  --sup_immed_triv                        [TrivRules]
% 2.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_immed_bw_main                     []
% 2.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  
% 2.22/1.02  ------ Combination Options
% 2.22/1.02  
% 2.22/1.02  --comb_res_mult                         3
% 2.22/1.02  --comb_sup_mult                         2
% 2.22/1.02  --comb_inst_mult                        10
% 2.22/1.02  
% 2.22/1.02  ------ Debug Options
% 2.22/1.02  
% 2.22/1.02  --dbg_backtrace                         false
% 2.22/1.02  --dbg_dump_prop_clauses                 false
% 2.22/1.02  --dbg_dump_prop_clauses_file            -
% 2.22/1.02  --dbg_out_stat                          false
% 2.22/1.02  ------ Parsing...
% 2.22/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/1.02  ------ Proving...
% 2.22/1.02  ------ Problem Properties 
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  clauses                                 17
% 2.22/1.02  conjectures                             6
% 2.22/1.02  EPR                                     9
% 2.22/1.02  Horn                                    15
% 2.22/1.02  unary                                   7
% 2.22/1.02  binary                                  1
% 2.22/1.02  lits                                    41
% 2.22/1.02  lits eq                                 3
% 2.22/1.02  fd_pure                                 0
% 2.22/1.02  fd_pseudo                               0
% 2.22/1.02  fd_cond                                 0
% 2.22/1.02  fd_pseudo_cond                          1
% 2.22/1.02  AC symbols                              0
% 2.22/1.02  
% 2.22/1.02  ------ Schedule dynamic 5 is on 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  ------ 
% 2.22/1.02  Current options:
% 2.22/1.02  ------ 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options
% 2.22/1.02  
% 2.22/1.02  --out_options                           all
% 2.22/1.02  --tptp_safe_out                         true
% 2.22/1.02  --problem_path                          ""
% 2.22/1.02  --include_path                          ""
% 2.22/1.02  --clausifier                            res/vclausify_rel
% 2.22/1.02  --clausifier_options                    --mode clausify
% 2.22/1.02  --stdin                                 false
% 2.22/1.02  --stats_out                             all
% 2.22/1.02  
% 2.22/1.02  ------ General Options
% 2.22/1.02  
% 2.22/1.02  --fof                                   false
% 2.22/1.02  --time_out_real                         305.
% 2.22/1.02  --time_out_virtual                      -1.
% 2.22/1.02  --symbol_type_check                     false
% 2.22/1.02  --clausify_out                          false
% 2.22/1.02  --sig_cnt_out                           false
% 2.22/1.02  --trig_cnt_out                          false
% 2.22/1.02  --trig_cnt_out_tolerance                1.
% 2.22/1.02  --trig_cnt_out_sk_spl                   false
% 2.22/1.02  --abstr_cl_out                          false
% 2.22/1.02  
% 2.22/1.02  ------ Global Options
% 2.22/1.02  
% 2.22/1.02  --schedule                              default
% 2.22/1.02  --add_important_lit                     false
% 2.22/1.02  --prop_solver_per_cl                    1000
% 2.22/1.02  --min_unsat_core                        false
% 2.22/1.02  --soft_assumptions                      false
% 2.22/1.02  --soft_lemma_size                       3
% 2.22/1.02  --prop_impl_unit_size                   0
% 2.22/1.02  --prop_impl_unit                        []
% 2.22/1.02  --share_sel_clauses                     true
% 2.22/1.02  --reset_solvers                         false
% 2.22/1.02  --bc_imp_inh                            [conj_cone]
% 2.22/1.02  --conj_cone_tolerance                   3.
% 2.22/1.02  --extra_neg_conj                        none
% 2.22/1.02  --large_theory_mode                     true
% 2.22/1.02  --prolific_symb_bound                   200
% 2.22/1.02  --lt_threshold                          2000
% 2.22/1.02  --clause_weak_htbl                      true
% 2.22/1.02  --gc_record_bc_elim                     false
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing Options
% 2.22/1.02  
% 2.22/1.02  --preprocessing_flag                    true
% 2.22/1.02  --time_out_prep_mult                    0.1
% 2.22/1.02  --splitting_mode                        input
% 2.22/1.02  --splitting_grd                         true
% 2.22/1.02  --splitting_cvd                         false
% 2.22/1.02  --splitting_cvd_svl                     false
% 2.22/1.02  --splitting_nvd                         32
% 2.22/1.02  --sub_typing                            true
% 2.22/1.02  --prep_gs_sim                           true
% 2.22/1.02  --prep_unflatten                        true
% 2.22/1.02  --prep_res_sim                          true
% 2.22/1.02  --prep_upred                            true
% 2.22/1.02  --prep_sem_filter                       exhaustive
% 2.22/1.02  --prep_sem_filter_out                   false
% 2.22/1.02  --pred_elim                             true
% 2.22/1.02  --res_sim_input                         true
% 2.22/1.02  --eq_ax_congr_red                       true
% 2.22/1.02  --pure_diseq_elim                       true
% 2.22/1.02  --brand_transform                       false
% 2.22/1.02  --non_eq_to_eq                          false
% 2.22/1.02  --prep_def_merge                        true
% 2.22/1.02  --prep_def_merge_prop_impl              false
% 2.22/1.02  --prep_def_merge_mbd                    true
% 2.22/1.02  --prep_def_merge_tr_red                 false
% 2.22/1.02  --prep_def_merge_tr_cl                  false
% 2.22/1.02  --smt_preprocessing                     true
% 2.22/1.02  --smt_ac_axioms                         fast
% 2.22/1.02  --preprocessed_out                      false
% 2.22/1.02  --preprocessed_stats                    false
% 2.22/1.02  
% 2.22/1.02  ------ Abstraction refinement Options
% 2.22/1.02  
% 2.22/1.02  --abstr_ref                             []
% 2.22/1.02  --abstr_ref_prep                        false
% 2.22/1.02  --abstr_ref_until_sat                   false
% 2.22/1.02  --abstr_ref_sig_restrict                funpre
% 2.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.02  --abstr_ref_under                       []
% 2.22/1.02  
% 2.22/1.02  ------ SAT Options
% 2.22/1.02  
% 2.22/1.02  --sat_mode                              false
% 2.22/1.02  --sat_fm_restart_options                ""
% 2.22/1.02  --sat_gr_def                            false
% 2.22/1.02  --sat_epr_types                         true
% 2.22/1.02  --sat_non_cyclic_types                  false
% 2.22/1.02  --sat_finite_models                     false
% 2.22/1.02  --sat_fm_lemmas                         false
% 2.22/1.02  --sat_fm_prep                           false
% 2.22/1.02  --sat_fm_uc_incr                        true
% 2.22/1.02  --sat_out_model                         small
% 2.22/1.02  --sat_out_clauses                       false
% 2.22/1.02  
% 2.22/1.02  ------ QBF Options
% 2.22/1.02  
% 2.22/1.02  --qbf_mode                              false
% 2.22/1.02  --qbf_elim_univ                         false
% 2.22/1.02  --qbf_dom_inst                          none
% 2.22/1.02  --qbf_dom_pre_inst                      false
% 2.22/1.02  --qbf_sk_in                             false
% 2.22/1.02  --qbf_pred_elim                         true
% 2.22/1.02  --qbf_split                             512
% 2.22/1.02  
% 2.22/1.02  ------ BMC1 Options
% 2.22/1.02  
% 2.22/1.02  --bmc1_incremental                      false
% 2.22/1.02  --bmc1_axioms                           reachable_all
% 2.22/1.02  --bmc1_min_bound                        0
% 2.22/1.02  --bmc1_max_bound                        -1
% 2.22/1.02  --bmc1_max_bound_default                -1
% 2.22/1.02  --bmc1_symbol_reachability              true
% 2.22/1.02  --bmc1_property_lemmas                  false
% 2.22/1.02  --bmc1_k_induction                      false
% 2.22/1.02  --bmc1_non_equiv_states                 false
% 2.22/1.02  --bmc1_deadlock                         false
% 2.22/1.02  --bmc1_ucm                              false
% 2.22/1.02  --bmc1_add_unsat_core                   none
% 2.22/1.02  --bmc1_unsat_core_children              false
% 2.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.02  --bmc1_out_stat                         full
% 2.22/1.02  --bmc1_ground_init                      false
% 2.22/1.02  --bmc1_pre_inst_next_state              false
% 2.22/1.02  --bmc1_pre_inst_state                   false
% 2.22/1.02  --bmc1_pre_inst_reach_state             false
% 2.22/1.02  --bmc1_out_unsat_core                   false
% 2.22/1.02  --bmc1_aig_witness_out                  false
% 2.22/1.02  --bmc1_verbose                          false
% 2.22/1.02  --bmc1_dump_clauses_tptp                false
% 2.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.02  --bmc1_dump_file                        -
% 2.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.02  --bmc1_ucm_extend_mode                  1
% 2.22/1.02  --bmc1_ucm_init_mode                    2
% 2.22/1.02  --bmc1_ucm_cone_mode                    none
% 2.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.02  --bmc1_ucm_relax_model                  4
% 2.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.02  --bmc1_ucm_layered_model                none
% 2.22/1.02  --bmc1_ucm_max_lemma_size               10
% 2.22/1.02  
% 2.22/1.02  ------ AIG Options
% 2.22/1.02  
% 2.22/1.02  --aig_mode                              false
% 2.22/1.02  
% 2.22/1.02  ------ Instantiation Options
% 2.22/1.02  
% 2.22/1.02  --instantiation_flag                    true
% 2.22/1.02  --inst_sos_flag                         false
% 2.22/1.02  --inst_sos_phase                        true
% 2.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel_side                     none
% 2.22/1.02  --inst_solver_per_active                1400
% 2.22/1.02  --inst_solver_calls_frac                1.
% 2.22/1.02  --inst_passive_queue_type               priority_queues
% 2.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.02  --inst_passive_queues_freq              [25;2]
% 2.22/1.02  --inst_dismatching                      true
% 2.22/1.02  --inst_eager_unprocessed_to_passive     true
% 2.22/1.02  --inst_prop_sim_given                   true
% 2.22/1.02  --inst_prop_sim_new                     false
% 2.22/1.02  --inst_subs_new                         false
% 2.22/1.02  --inst_eq_res_simp                      false
% 2.22/1.02  --inst_subs_given                       false
% 2.22/1.02  --inst_orphan_elimination               true
% 2.22/1.02  --inst_learning_loop_flag               true
% 2.22/1.02  --inst_learning_start                   3000
% 2.22/1.02  --inst_learning_factor                  2
% 2.22/1.02  --inst_start_prop_sim_after_learn       3
% 2.22/1.02  --inst_sel_renew                        solver
% 2.22/1.02  --inst_lit_activity_flag                true
% 2.22/1.02  --inst_restr_to_given                   false
% 2.22/1.02  --inst_activity_threshold               500
% 2.22/1.02  --inst_out_proof                        true
% 2.22/1.02  
% 2.22/1.02  ------ Resolution Options
% 2.22/1.02  
% 2.22/1.02  --resolution_flag                       false
% 2.22/1.02  --res_lit_sel                           adaptive
% 2.22/1.02  --res_lit_sel_side                      none
% 2.22/1.02  --res_ordering                          kbo
% 2.22/1.02  --res_to_prop_solver                    active
% 2.22/1.02  --res_prop_simpl_new                    false
% 2.22/1.02  --res_prop_simpl_given                  true
% 2.22/1.02  --res_passive_queue_type                priority_queues
% 2.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.02  --res_passive_queues_freq               [15;5]
% 2.22/1.02  --res_forward_subs                      full
% 2.22/1.02  --res_backward_subs                     full
% 2.22/1.02  --res_forward_subs_resolution           true
% 2.22/1.02  --res_backward_subs_resolution          true
% 2.22/1.02  --res_orphan_elimination                true
% 2.22/1.02  --res_time_limit                        2.
% 2.22/1.02  --res_out_proof                         true
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Options
% 2.22/1.02  
% 2.22/1.02  --superposition_flag                    true
% 2.22/1.02  --sup_passive_queue_type                priority_queues
% 2.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.02  --demod_completeness_check              fast
% 2.22/1.02  --demod_use_ground                      true
% 2.22/1.02  --sup_to_prop_solver                    passive
% 2.22/1.02  --sup_prop_simpl_new                    true
% 2.22/1.02  --sup_prop_simpl_given                  true
% 2.22/1.02  --sup_fun_splitting                     false
% 2.22/1.02  --sup_smt_interval                      50000
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Simplification Setup
% 2.22/1.02  
% 2.22/1.02  --sup_indices_passive                   []
% 2.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_full_bw                           [BwDemod]
% 2.22/1.02  --sup_immed_triv                        [TrivRules]
% 2.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_immed_bw_main                     []
% 2.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  
% 2.22/1.02  ------ Combination Options
% 2.22/1.02  
% 2.22/1.02  --comb_res_mult                         3
% 2.22/1.02  --comb_sup_mult                         2
% 2.22/1.02  --comb_inst_mult                        10
% 2.22/1.02  
% 2.22/1.02  ------ Debug Options
% 2.22/1.02  
% 2.22/1.02  --dbg_backtrace                         false
% 2.22/1.02  --dbg_dump_prop_clauses                 false
% 2.22/1.02  --dbg_dump_prop_clauses_file            -
% 2.22/1.02  --dbg_out_stat                          false
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  ------ Proving...
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  % SZS status Theorem for theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  fof(f5,axiom,(
% 2.22/1.02    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f13,plain,(
% 2.22/1.02    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f5])).
% 2.22/1.02  
% 2.22/1.02  fof(f37,plain,(
% 2.22/1.02    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f13])).
% 2.22/1.02  
% 2.22/1.02  fof(f8,conjecture,(
% 2.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 2.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f9,negated_conjecture,(
% 2.22/1.02    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 2.22/1.02    inference(negated_conjecture,[],[f8])).
% 2.22/1.02  
% 2.22/1.02  fof(f17,plain,(
% 2.22/1.02    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f9])).
% 2.22/1.02  
% 2.22/1.02  fof(f18,plain,(
% 2.22/1.02    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 2.22/1.02    inference(flattening,[],[f17])).
% 2.22/1.02  
% 2.22/1.02  fof(f28,plain,(
% 2.22/1.02    ( ! [X0,X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) => (~v1_tex_2(sK3,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(sK3,X0))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f27,plain,(
% 2.22/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(sK2,X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK2,X0))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f26,plain,(
% 2.22/1.02    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK1) & v1_tex_2(X1,sK1) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK1)) & m1_pre_topc(X1,sK1)) & l1_pre_topc(sK1))),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f29,plain,(
% 2.22/1.02    ((~v1_tex_2(sK3,sK1) & v1_tex_2(sK2,sK1) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_pre_topc(sK3,sK1)) & m1_pre_topc(sK2,sK1)) & l1_pre_topc(sK1)),
% 2.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f28,f27,f26])).
% 2.22/1.02  
% 2.22/1.02  fof(f46,plain,(
% 2.22/1.02    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 2.22/1.02    inference(cnf_transformation,[],[f29])).
% 2.22/1.02  
% 2.22/1.02  fof(f4,axiom,(
% 2.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f12,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f4])).
% 2.22/1.02  
% 2.22/1.02  fof(f21,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.22/1.02    inference(nnf_transformation,[],[f12])).
% 2.22/1.02  
% 2.22/1.02  fof(f35,plain,(
% 2.22/1.02    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f21])).
% 2.22/1.02  
% 2.22/1.02  fof(f2,axiom,(
% 2.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f10,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f2])).
% 2.22/1.02  
% 2.22/1.02  fof(f33,plain,(
% 2.22/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f10])).
% 2.22/1.02  
% 2.22/1.02  fof(f43,plain,(
% 2.22/1.02    l1_pre_topc(sK1)),
% 2.22/1.02    inference(cnf_transformation,[],[f29])).
% 2.22/1.02  
% 2.22/1.02  fof(f44,plain,(
% 2.22/1.02    m1_pre_topc(sK2,sK1)),
% 2.22/1.02    inference(cnf_transformation,[],[f29])).
% 2.22/1.02  
% 2.22/1.02  fof(f3,axiom,(
% 2.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 2.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f11,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.22/1.03    inference(ennf_transformation,[],[f3])).
% 2.22/1.03  
% 2.22/1.03  fof(f34,plain,(
% 2.22/1.03    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f11])).
% 2.22/1.03  
% 2.22/1.03  fof(f45,plain,(
% 2.22/1.03    m1_pre_topc(sK3,sK1)),
% 2.22/1.03    inference(cnf_transformation,[],[f29])).
% 2.22/1.03  
% 2.22/1.03  fof(f6,axiom,(
% 2.22/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f14,plain,(
% 2.22/1.03    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.03    inference(ennf_transformation,[],[f6])).
% 2.22/1.03  
% 2.22/1.03  fof(f38,plain,(
% 2.22/1.03    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f14])).
% 2.22/1.03  
% 2.22/1.03  fof(f1,axiom,(
% 2.22/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f19,plain,(
% 2.22/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/1.03    inference(nnf_transformation,[],[f1])).
% 2.22/1.03  
% 2.22/1.03  fof(f20,plain,(
% 2.22/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/1.03    inference(flattening,[],[f19])).
% 2.22/1.03  
% 2.22/1.03  fof(f32,plain,(
% 2.22/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f20])).
% 2.22/1.03  
% 2.22/1.03  fof(f7,axiom,(
% 2.22/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f15,plain,(
% 2.22/1.03    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.03    inference(ennf_transformation,[],[f7])).
% 2.22/1.03  
% 2.22/1.03  fof(f16,plain,(
% 2.22/1.03    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.03    inference(flattening,[],[f15])).
% 2.22/1.03  
% 2.22/1.03  fof(f22,plain,(
% 2.22/1.03    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.03    inference(nnf_transformation,[],[f16])).
% 2.22/1.03  
% 2.22/1.03  fof(f23,plain,(
% 2.22/1.03    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.03    inference(rectify,[],[f22])).
% 2.22/1.03  
% 2.22/1.03  fof(f24,plain,(
% 2.22/1.03    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.22/1.03    introduced(choice_axiom,[])).
% 2.22/1.03  
% 2.22/1.03  fof(f25,plain,(
% 2.22/1.03    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.22/1.03  
% 2.22/1.03  fof(f39,plain,(
% 2.22/1.03    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f25])).
% 2.22/1.03  
% 2.22/1.03  fof(f51,plain,(
% 2.22/1.03    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.03    inference(equality_resolution,[],[f39])).
% 2.22/1.03  
% 2.22/1.03  fof(f41,plain,(
% 2.22/1.03    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f25])).
% 2.22/1.03  
% 2.22/1.03  fof(f48,plain,(
% 2.22/1.03    ~v1_tex_2(sK3,sK1)),
% 2.22/1.03    inference(cnf_transformation,[],[f29])).
% 2.22/1.03  
% 2.22/1.03  fof(f42,plain,(
% 2.22/1.03    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f25])).
% 2.22/1.03  
% 2.22/1.03  fof(f40,plain,(
% 2.22/1.03    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f25])).
% 2.22/1.03  
% 2.22/1.03  fof(f47,plain,(
% 2.22/1.03    v1_tex_2(sK2,sK1)),
% 2.22/1.03    inference(cnf_transformation,[],[f29])).
% 2.22/1.03  
% 2.22/1.03  cnf(c_7,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1061,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X0) = iProver_top
% 2.22/1.03      | l1_pre_topc(X0) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_15,negated_conjecture,
% 2.22/1.03      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 2.22/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_6,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.22/1.03      | ~ l1_pre_topc(X0)
% 2.22/1.03      | ~ l1_pre_topc(X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_103,plain,
% 2.22/1.03      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.22/1.03      | ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ l1_pre_topc(X1) ),
% 2.22/1.03      inference(global_propositional_subsumption,[status(thm)],[c_6,c_3]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_104,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.22/1.03      | ~ l1_pre_topc(X1) ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_103]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1050,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_104]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1315,plain,
% 2.22/1.03      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK2) != iProver_top
% 2.22/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_15,c_1050]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_18,negated_conjecture,
% 2.22/1.03      ( l1_pre_topc(sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_19,plain,
% 2.22/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_17,negated_conjecture,
% 2.22/1.03      ( m1_pre_topc(sK2,sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1052,plain,
% 2.22/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1063,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top
% 2.22/1.03      | l1_pre_topc(X0) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1326,plain,
% 2.22/1.03      ( l1_pre_topc(sK2) = iProver_top
% 2.22/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1052,c_1063]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1522,plain,
% 2.22/1.03      ( m1_pre_topc(X0,sK2) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_1315,c_19,c_1326]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1523,plain,
% 2.22/1.03      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK2) != iProver_top ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_1522]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.22/1.03      | ~ l1_pre_topc(X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f34]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1062,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X1) = iProver_top
% 2.22/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1531,plain,
% 2.22/1.03      ( m1_pre_topc(X0,sK2) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK3) = iProver_top
% 2.22/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1523,c_1062]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_16,negated_conjecture,
% 2.22/1.03      ( m1_pre_topc(sK3,sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1053,plain,
% 2.22/1.03      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1325,plain,
% 2.22/1.03      ( l1_pre_topc(sK1) != iProver_top
% 2.22/1.03      | l1_pre_topc(sK3) = iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1053,c_1063]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1715,plain,
% 2.22/1.03      ( m1_pre_topc(X0,sK3) = iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK2) != iProver_top ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_1531,c_19,c_1325]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1716,plain,
% 2.22/1.03      ( m1_pre_topc(X0,sK2) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK3) = iProver_top ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_1715]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1723,plain,
% 2.22/1.03      ( m1_pre_topc(sK2,sK3) = iProver_top
% 2.22/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1061,c_1716]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2233,plain,
% 2.22/1.03      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_1723,c_19,c_1326]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_8,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.03      | ~ l1_pre_topc(X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1060,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 2.22/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_0,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.22/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1065,plain,
% 2.22/1.03      ( X0 = X1
% 2.22/1.03      | r1_tarski(X0,X1) != iProver_top
% 2.22/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1395,plain,
% 2.22/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.22/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 2.22/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.22/1.03      | l1_pre_topc(X0) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1060,c_1065]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2586,plain,
% 2.22/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.22/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 2.22/1.03      | l1_pre_topc(X0) != iProver_top
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1060,c_1395]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_47,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top
% 2.22/1.03      | l1_pre_topc(X0) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3553,plain,
% 2.22/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 2.22/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 2.22/1.03      | u1_struct_0(X0) = u1_struct_0(X1)
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_2586,c_47]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3554,plain,
% 2.22/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.22/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 2.22/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_3553]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3569,plain,
% 2.22/1.03      ( u1_struct_0(sK3) = u1_struct_0(sK2)
% 2.22/1.03      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.22/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_2233,c_3554]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1502,plain,
% 2.22/1.03      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK2) = iProver_top
% 2.22/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_15,c_1062]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1612,plain,
% 2.22/1.03      ( m1_pre_topc(X0,sK2) = iProver_top
% 2.22/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_1502,c_19,c_1326]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1613,plain,
% 2.22/1.03      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK2) = iProver_top ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_1612]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1620,plain,
% 2.22/1.03      ( m1_pre_topc(X0,sK2) = iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK3) != iProver_top
% 2.22/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1050,c_1613]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1794,plain,
% 2.22/1.03      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK2) = iProver_top ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_1620,c_19,c_1325]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1795,plain,
% 2.22/1.03      ( m1_pre_topc(X0,sK2) = iProver_top
% 2.22/1.03      | m1_pre_topc(X0,sK3) != iProver_top ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_1794]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1802,plain,
% 2.22/1.03      ( m1_pre_topc(sK3,sK2) = iProver_top
% 2.22/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1061,c_1795]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4384,plain,
% 2.22/1.03      ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_3569,c_19,c_1325,c_1802]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_12,plain,
% 2.22/1.03      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/1.03      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.03      | ~ v1_tex_2(X0,X1)
% 2.22/1.03      | ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ l1_pre_topc(X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1056,plain,
% 2.22/1.03      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.22/1.03      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.22/1.03      | v1_tex_2(X0,X1) != iProver_top
% 2.22/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 2.22/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4425,plain,
% 2.22/1.03      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.22/1.03      | v1_subset_1(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 2.22/1.03      | v1_tex_2(sK2,X0) != iProver_top
% 2.22/1.03      | m1_pre_topc(sK2,X0) != iProver_top
% 2.22/1.03      | l1_pre_topc(X0) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_4384,c_1056]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4481,plain,
% 2.22/1.03      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.22/1.03      | v1_subset_1(u1_struct_0(sK3),u1_struct_0(X0)) = iProver_top
% 2.22/1.03      | v1_tex_2(sK2,X0) != iProver_top
% 2.22/1.03      | m1_pre_topc(sK2,X0) != iProver_top
% 2.22/1.03      | l1_pre_topc(X0) != iProver_top ),
% 2.22/1.03      inference(light_normalisation,[status(thm)],[c_4425,c_4384]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4564,plain,
% 2.22/1.03      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.22/1.03      | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 2.22/1.03      | v1_tex_2(sK2,sK1) != iProver_top
% 2.22/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.22/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_4481]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_10,plain,
% 2.22/1.03      ( v1_tex_2(X0,X1)
% 2.22/1.03      | ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1058,plain,
% 2.22/1.03      ( sK0(X0,X1) = u1_struct_0(X1)
% 2.22/1.03      | v1_tex_2(X1,X0) = iProver_top
% 2.22/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 2.22/1.03      | l1_pre_topc(X0) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1976,plain,
% 2.22/1.03      ( sK0(sK1,sK3) = u1_struct_0(sK3)
% 2.22/1.03      | v1_tex_2(sK3,sK1) = iProver_top
% 2.22/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1053,c_1058]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_13,negated_conjecture,
% 2.22/1.03      ( ~ v1_tex_2(sK3,sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_357,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | sK0(X1,X0) = u1_struct_0(X0)
% 2.22/1.03      | sK1 != X1
% 2.22/1.03      | sK3 != X0 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_358,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK3,sK1)
% 2.22/1.03      | ~ l1_pre_topc(sK1)
% 2.22/1.03      | sK0(sK1,sK3) = u1_struct_0(sK3) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_357]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2127,plain,
% 2.22/1.03      ( sK0(sK1,sK3) = u1_struct_0(sK3) ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_1976,c_18,c_16,c_358]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_9,plain,
% 2.22/1.03      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 2.22/1.03      | v1_tex_2(X1,X0)
% 2.22/1.03      | ~ m1_pre_topc(X1,X0)
% 2.22/1.03      | ~ l1_pre_topc(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1059,plain,
% 2.22/1.03      ( v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) != iProver_top
% 2.22/1.03      | v1_tex_2(X1,X0) = iProver_top
% 2.22/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 2.22/1.03      | l1_pre_topc(X0) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2130,plain,
% 2.22/1.03      ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.22/1.03      | v1_tex_2(sK3,sK1) = iProver_top
% 2.22/1.03      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.22/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_2127,c_1059]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_722,plain,( X0 = X0 ),theory(equality) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1582,plain,
% 2.22/1.03      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_722]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_733,plain,
% 2.22/1.03      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.22/1.03      theory(equality) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1211,plain,
% 2.22/1.03      ( m1_subset_1(X0,X1)
% 2.22/1.03      | ~ m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/1.03      | X0 != sK0(sK1,sK3)
% 2.22/1.03      | X1 != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_733]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1360,plain,
% 2.22/1.03      ( ~ m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/1.03      | m1_subset_1(u1_struct_0(sK3),X0)
% 2.22/1.03      | X0 != k1_zfmisc_1(u1_struct_0(sK1))
% 2.22/1.03      | u1_struct_0(sK3) != sK0(sK1,sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1211]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1567,plain,
% 2.22/1.03      ( ~ m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/1.03      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.03      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.22/1.03      | u1_struct_0(sK3) != sK0(sK1,sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1360]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1569,plain,
% 2.22/1.03      ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.22/1.03      | u1_struct_0(sK3) != sK0(sK1,sK3)
% 2.22/1.03      | m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.22/1.03      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1571,plain,
% 2.22/1.03      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.22/1.03      | u1_struct_0(sK3) != sK0(sK1,sK3)
% 2.22/1.03      | m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.22/1.03      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1569]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1350,plain,
% 2.22/1.03      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_722]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_723,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1256,plain,
% 2.22/1.03      ( X0 != X1 | X0 = sK0(sK1,sK3) | sK0(sK1,sK3) != X1 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_723]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1297,plain,
% 2.22/1.03      ( X0 = sK0(sK1,sK3)
% 2.22/1.03      | X0 != u1_struct_0(sK3)
% 2.22/1.03      | sK0(sK1,sK3) != u1_struct_0(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1256]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1349,plain,
% 2.22/1.03      ( sK0(sK1,sK3) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(sK3) = sK0(sK1,sK3)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1297]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_11,plain,
% 2.22/1.03      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.03      | v1_tex_2(X1,X0)
% 2.22/1.03      | ~ m1_pre_topc(X1,X0)
% 2.22/1.03      | ~ l1_pre_topc(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_335,plain,
% 2.22/1.03      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.03      | ~ m1_pre_topc(X1,X0)
% 2.22/1.03      | ~ l1_pre_topc(X0)
% 2.22/1.03      | sK1 != X0
% 2.22/1.03      | sK3 != X1 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_336,plain,
% 2.22/1.03      ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/1.03      | ~ m1_pre_topc(sK3,sK1)
% 2.22/1.03      | ~ l1_pre_topc(sK1) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_335]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_337,plain,
% 2.22/1.03      ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.22/1.03      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.22/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_23,plain,
% 2.22/1.03      ( v1_tex_2(sK3,sK1) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_14,negated_conjecture,
% 2.22/1.03      ( v1_tex_2(sK2,sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_22,plain,
% 2.22/1.03      ( v1_tex_2(sK2,sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_21,plain,
% 2.22/1.03      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_20,plain,
% 2.22/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(contradiction,plain,
% 2.22/1.03      ( $false ),
% 2.22/1.03      inference(minisat,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_4564,c_2130,c_1582,c_1571,c_1350,c_1349,c_358,c_337,
% 2.22/1.03                 c_23,c_22,c_21,c_16,c_20,c_19,c_18]) ).
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/1.03  
% 2.22/1.03  ------                               Statistics
% 2.22/1.03  
% 2.22/1.03  ------ General
% 2.22/1.03  
% 2.22/1.03  abstr_ref_over_cycles:                  0
% 2.22/1.03  abstr_ref_under_cycles:                 0
% 2.22/1.03  gc_basic_clause_elim:                   0
% 2.22/1.03  forced_gc_time:                         0
% 2.22/1.03  parsing_time:                           0.013
% 2.22/1.03  unif_index_cands_time:                  0.
% 2.22/1.03  unif_index_add_time:                    0.
% 2.22/1.03  orderings_time:                         0.
% 2.22/1.03  out_proof_time:                         0.009
% 2.22/1.03  total_time:                             0.189
% 2.22/1.03  num_of_symbols:                         45
% 2.22/1.03  num_of_terms:                           2033
% 2.22/1.03  
% 2.22/1.03  ------ Preprocessing
% 2.22/1.03  
% 2.22/1.03  num_of_splits:                          0
% 2.22/1.03  num_of_split_atoms:                     0
% 2.22/1.03  num_of_reused_defs:                     0
% 2.22/1.03  num_eq_ax_congr_red:                    6
% 2.22/1.03  num_of_sem_filtered_clauses:            1
% 2.22/1.03  num_of_subtypes:                        0
% 2.22/1.03  monotx_restored_types:                  0
% 2.22/1.03  sat_num_of_epr_types:                   0
% 2.22/1.03  sat_num_of_non_cyclic_types:            0
% 2.22/1.03  sat_guarded_non_collapsed_types:        0
% 2.22/1.03  num_pure_diseq_elim:                    0
% 2.22/1.03  simp_replaced_by:                       0
% 2.22/1.03  res_preprocessed:                       93
% 2.22/1.03  prep_upred:                             0
% 2.22/1.03  prep_unflattend:                        24
% 2.22/1.03  smt_new_axioms:                         0
% 2.22/1.03  pred_elim_cands:                        6
% 2.22/1.03  pred_elim:                              0
% 2.22/1.03  pred_elim_cl:                           0
% 2.22/1.03  pred_elim_cycles:                       6
% 2.22/1.03  merged_defs:                            0
% 2.22/1.03  merged_defs_ncl:                        0
% 2.22/1.03  bin_hyper_res:                          0
% 2.22/1.03  prep_cycles:                            4
% 2.22/1.03  pred_elim_time:                         0.006
% 2.22/1.03  splitting_time:                         0.
% 2.22/1.03  sem_filter_time:                        0.
% 2.22/1.03  monotx_time:                            0.
% 2.22/1.03  subtype_inf_time:                       0.
% 2.22/1.03  
% 2.22/1.03  ------ Problem properties
% 2.22/1.03  
% 2.22/1.03  clauses:                                17
% 2.22/1.03  conjectures:                            6
% 2.22/1.03  epr:                                    9
% 2.22/1.03  horn:                                   15
% 2.22/1.03  ground:                                 6
% 2.22/1.03  unary:                                  7
% 2.22/1.03  binary:                                 1
% 2.22/1.03  lits:                                   41
% 2.22/1.03  lits_eq:                                3
% 2.22/1.03  fd_pure:                                0
% 2.22/1.03  fd_pseudo:                              0
% 2.22/1.03  fd_cond:                                0
% 2.22/1.03  fd_pseudo_cond:                         1
% 2.22/1.03  ac_symbols:                             0
% 2.22/1.03  
% 2.22/1.03  ------ Propositional Solver
% 2.22/1.03  
% 2.22/1.03  prop_solver_calls:                      32
% 2.22/1.03  prop_fast_solver_calls:                 823
% 2.22/1.03  smt_solver_calls:                       0
% 2.22/1.03  smt_fast_solver_calls:                  0
% 2.22/1.03  prop_num_of_clauses:                    1122
% 2.22/1.03  prop_preprocess_simplified:             4456
% 2.22/1.03  prop_fo_subsumed:                       54
% 2.22/1.03  prop_solver_time:                       0.
% 2.22/1.03  smt_solver_time:                        0.
% 2.22/1.03  smt_fast_solver_time:                   0.
% 2.22/1.03  prop_fast_solver_time:                  0.
% 2.22/1.03  prop_unsat_core_time:                   0.
% 2.22/1.03  
% 2.22/1.03  ------ QBF
% 2.22/1.03  
% 2.22/1.03  qbf_q_res:                              0
% 2.22/1.03  qbf_num_tautologies:                    0
% 2.22/1.03  qbf_prep_cycles:                        0
% 2.22/1.03  
% 2.22/1.03  ------ BMC1
% 2.22/1.03  
% 2.22/1.03  bmc1_current_bound:                     -1
% 2.22/1.03  bmc1_last_solved_bound:                 -1
% 2.22/1.03  bmc1_unsat_core_size:                   -1
% 2.22/1.03  bmc1_unsat_core_parents_size:           -1
% 2.22/1.03  bmc1_merge_next_fun:                    0
% 2.22/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.22/1.03  
% 2.22/1.03  ------ Instantiation
% 2.22/1.03  
% 2.22/1.03  inst_num_of_clauses:                    419
% 2.22/1.03  inst_num_in_passive:                    136
% 2.22/1.03  inst_num_in_active:                     276
% 2.22/1.03  inst_num_in_unprocessed:                7
% 2.22/1.03  inst_num_of_loops:                      290
% 2.22/1.03  inst_num_of_learning_restarts:          0
% 2.22/1.03  inst_num_moves_active_passive:          6
% 2.22/1.03  inst_lit_activity:                      0
% 2.22/1.03  inst_lit_activity_moves:                0
% 2.22/1.03  inst_num_tautologies:                   0
% 2.22/1.03  inst_num_prop_implied:                  0
% 2.22/1.03  inst_num_existing_simplified:           0
% 2.22/1.03  inst_num_eq_res_simplified:             0
% 2.22/1.03  inst_num_child_elim:                    0
% 2.22/1.03  inst_num_of_dismatching_blockings:      73
% 2.22/1.03  inst_num_of_non_proper_insts:           719
% 2.22/1.03  inst_num_of_duplicates:                 0
% 2.22/1.03  inst_inst_num_from_inst_to_res:         0
% 2.22/1.03  inst_dismatching_checking_time:         0.
% 2.22/1.03  
% 2.22/1.03  ------ Resolution
% 2.22/1.03  
% 2.22/1.03  res_num_of_clauses:                     0
% 2.22/1.03  res_num_in_passive:                     0
% 2.22/1.03  res_num_in_active:                      0
% 2.22/1.03  res_num_of_loops:                       97
% 2.22/1.03  res_forward_subset_subsumed:            157
% 2.22/1.03  res_backward_subset_subsumed:           0
% 2.22/1.03  res_forward_subsumed:                   0
% 2.22/1.03  res_backward_subsumed:                  0
% 2.22/1.03  res_forward_subsumption_resolution:     0
% 2.22/1.03  res_backward_subsumption_resolution:    0
% 2.22/1.03  res_clause_to_clause_subsumption:       332
% 2.22/1.03  res_orphan_elimination:                 0
% 2.22/1.03  res_tautology_del:                      91
% 2.22/1.03  res_num_eq_res_simplified:              0
% 2.22/1.03  res_num_sel_changes:                    0
% 2.22/1.03  res_moves_from_active_to_pass:          0
% 2.22/1.03  
% 2.22/1.03  ------ Superposition
% 2.22/1.03  
% 2.22/1.03  sup_time_total:                         0.
% 2.22/1.03  sup_time_generating:                    0.
% 2.22/1.03  sup_time_sim_full:                      0.
% 2.22/1.03  sup_time_sim_immed:                     0.
% 2.22/1.03  
% 2.22/1.03  sup_num_of_clauses:                     74
% 2.22/1.03  sup_num_in_active:                      51
% 2.22/1.03  sup_num_in_passive:                     23
% 2.22/1.03  sup_num_of_loops:                       56
% 2.22/1.03  sup_fw_superposition:                   52
% 2.22/1.03  sup_bw_superposition:                   48
% 2.22/1.03  sup_immediate_simplified:               21
% 2.22/1.03  sup_given_eliminated:                   0
% 2.22/1.03  comparisons_done:                       0
% 2.22/1.03  comparisons_avoided:                    0
% 2.22/1.03  
% 2.22/1.03  ------ Simplifications
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  sim_fw_subset_subsumed:                 7
% 2.22/1.03  sim_bw_subset_subsumed:                 1
% 2.22/1.03  sim_fw_subsumed:                        3
% 2.22/1.03  sim_bw_subsumed:                        2
% 2.22/1.03  sim_fw_subsumption_res:                 0
% 2.22/1.03  sim_bw_subsumption_res:                 0
% 2.22/1.03  sim_tautology_del:                      10
% 2.22/1.03  sim_eq_tautology_del:                   9
% 2.22/1.03  sim_eq_res_simp:                        0
% 2.22/1.03  sim_fw_demodulated:                     2
% 2.22/1.03  sim_bw_demodulated:                     6
% 2.22/1.03  sim_light_normalised:                   10
% 2.22/1.03  sim_joinable_taut:                      0
% 2.22/1.03  sim_joinable_simp:                      0
% 2.22/1.03  sim_ac_normalised:                      0
% 2.22/1.03  sim_smt_subsumption:                    0
% 2.22/1.03  
%------------------------------------------------------------------------------
