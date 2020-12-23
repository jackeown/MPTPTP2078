%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1883+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:46 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 340 expanded)
%              Number of clauses        :   38 (  64 expanded)
%              Number of leaves         :    6 (  96 expanded)
%              Depth                    :   23
%              Number of atoms          :  296 (2643 expanded)
%              Number of equality atoms :   64 ( 392 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v3_tex_2(X2,X0)
                  <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tex_2(X2,X0)
              <~> v4_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tex_2(X2,X0)
              <~> v4_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,X0)
                | ~ v3_tex_2(X2,X0) )
              & ( v4_tex_2(X1,X0)
                | v3_tex_2(X2,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,X0)
                | ~ v3_tex_2(X2,X0) )
              & ( v4_tex_2(X1,X0)
                | v3_tex_2(X2,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v4_tex_2(X1,X0)
            | ~ v3_tex_2(X2,X0) )
          & ( v4_tex_2(X1,X0)
            | v3_tex_2(X2,X0) )
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_tex_2(X1,X0)
          | ~ v3_tex_2(sK3,X0) )
        & ( v4_tex_2(X1,X0)
          | v3_tex_2(sK3,X0) )
        & u1_struct_0(X1) = sK3
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,X0)
                | ~ v3_tex_2(X2,X0) )
              & ( v4_tex_2(X1,X0)
                | v3_tex_2(X2,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ( ~ v4_tex_2(sK2,X0)
              | ~ v3_tex_2(X2,X0) )
            & ( v4_tex_2(sK2,X0)
              | v3_tex_2(X2,X0) )
            & u1_struct_0(sK2) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) )
                & ( v4_tex_2(X1,X0)
                  | v3_tex_2(X2,X0) )
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,sK1)
                | ~ v3_tex_2(X2,sK1) )
              & ( v4_tex_2(X1,sK1)
                | v3_tex_2(X2,sK1) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(X1,sK1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ( ~ v4_tex_2(sK2,sK1)
      | ~ v3_tex_2(sK3,sK1) )
    & ( v4_tex_2(sK2,sK1)
      | v3_tex_2(sK3,sK1) )
    & u1_struct_0(sK2) = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK1)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).

fof(f27,plain,
    ( v4_tex_2(sK2,sK1)
    | v3_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK0(X0,X1),X0)
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK0(X0,X1),X0)
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(sK0(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f23,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,
    ( ~ v4_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f26,plain,(
    u1_struct_0(sK2) = sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_5,negated_conjecture,
    ( v3_tex_2(sK3,sK1)
    | v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_73,plain,
    ( v3_tex_2(sK3,sK1)
    | v4_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_tex_2(sK0(X1,X0),X1)
    | v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_241,plain,
    ( ~ v3_tex_2(sK0(X0,X1),X0)
    | v4_tex_2(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_242,plain,
    ( ~ v3_tex_2(sK0(sK1,sK2),sK1)
    | v4_tex_2(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_10,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_244,plain,
    ( ~ v3_tex_2(sK0(sK1,sK2),sK1)
    | v4_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_10,c_9])).

cnf(c_320,plain,
    ( v4_tex_2(sK2,sK1)
    | sK0(sK1,sK2) != sK3
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_73,c_244])).

cnf(c_4,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK1)
    | ~ v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_71,plain,
    ( ~ v3_tex_2(sK3,sK1)
    | ~ v4_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_210,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_211,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tex_2(u1_struct_0(sK2),sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_213,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tex_2(u1_struct_0(sK2),sK1)
    | ~ v4_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_211,c_10,c_9])).

cnf(c_282,plain,
    ( v3_tex_2(u1_struct_0(sK2),sK1)
    | ~ v4_tex_2(sK2,sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_213])).

cnf(c_6,negated_conjecture,
    ( u1_struct_0(sK2) = sK3 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_284,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | ~ v4_tex_2(sK2,sK1)
    | v3_tex_2(u1_struct_0(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_6])).

cnf(c_285,plain,
    ( v3_tex_2(u1_struct_0(sK2),sK1)
    | ~ v4_tex_2(sK2,sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_304,plain,
    ( ~ v4_tex_2(sK2,sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != sK3
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_71,c_285])).

cnf(c_306,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | ~ v4_tex_2(sK2,sK1)
    | sK1 != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_6])).

cnf(c_307,plain,
    ( ~ v4_tex_2(sK2,sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK1 != sK1 ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_341,plain,
    ( sK0(sK1,sK2) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK1 != sK1 ),
    inference(resolution,[status(thm)],[c_320,c_307])).

cnf(c_368,plain,
    ( sK0(sK1,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_341])).

cnf(c_373,plain,
    ( sK0(sK1,sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_368])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_227,plain,
    ( v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_228,plain,
    ( v4_tex_2(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_230,plain,
    ( v4_tex_2(sK2,sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_10,c_9])).

cnf(c_351,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK1 != sK1 ),
    inference(resolution,[status(thm)],[c_230,c_307])).

cnf(c_367,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_351])).

cnf(c_374,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_375,negated_conjecture,
    ( u1_struct_0(sK2) = sK3 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_379,plain,
    ( sK0(sK1,sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_374,c_375])).

cnf(c_380,plain,
    ( sK3 != sK3 ),
    inference(light_normalisation,[status(thm)],[c_373,c_379])).

cnf(c_381,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_380])).


%------------------------------------------------------------------------------
