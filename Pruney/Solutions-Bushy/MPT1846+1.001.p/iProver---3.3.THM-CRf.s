%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1846+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:39 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 298 expanded)
%              Number of clauses        :   41 (  66 expanded)
%              Number of leaves         :    6 (  80 expanded)
%              Depth                    :   24
%              Number of atoms          :  275 (2049 expanded)
%              Number of equality atoms :   64 ( 340 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v1_subset_1(X2,u1_struct_0(X0))
                  <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v1_tex_2(X1,X0)
            | ~ v1_subset_1(X2,u1_struct_0(X0)) )
          & ( v1_tex_2(X1,X0)
            | v1_subset_1(X2,u1_struct_0(X0)) )
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v1_tex_2(X1,X0)
          | ~ v1_subset_1(sK3,u1_struct_0(X0)) )
        & ( v1_tex_2(X1,X0)
          | v1_subset_1(sK3,u1_struct_0(X0)) )
        & u1_struct_0(X1) = sK3
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ( ~ v1_tex_2(sK2,X0)
              | ~ v1_subset_1(X2,u1_struct_0(X0)) )
            & ( v1_tex_2(sK2,X0)
              | v1_subset_1(X2,u1_struct_0(X0)) )
            & u1_struct_0(sK2) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) )
                & ( v1_tex_2(X1,X0)
                  | v1_subset_1(X2,u1_struct_0(X0)) )
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,sK1)
                | ~ v1_subset_1(X2,u1_struct_0(sK1)) )
              & ( v1_tex_2(X1,sK1)
                | v1_subset_1(X2,u1_struct_0(sK1)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(X1,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ( ~ v1_tex_2(sK2,sK1)
      | ~ v1_subset_1(sK3,u1_struct_0(sK1)) )
    & ( v1_tex_2(sK2,sK1)
      | v1_subset_1(sK3,u1_struct_0(sK1)) )
    & u1_struct_0(sK2) = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).

fof(f26,plain,
    ( v1_tex_2(sK2,sK1)
    | v1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4])).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f22,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,
    ( ~ v1_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f25,plain,(
    u1_struct_0(sK2) = sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_5,negated_conjecture,
    ( v1_subset_1(sK3,u1_struct_0(sK1))
    | v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_67,plain,
    ( v1_tex_2(sK2,sK1)
    | v1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_68,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK1))
    | v1_tex_2(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_67])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_227,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_228,plain,
    ( ~ v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | v1_tex_2(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_230,plain,
    ( v1_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_9])).

cnf(c_231,plain,
    ( ~ v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | v1_tex_2(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_306,plain,
    ( v1_tex_2(sK2,sK1)
    | sK0(sK1,sK2) != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_68,c_231])).

cnf(c_4,negated_conjecture,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_65,plain,
    ( ~ v1_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_66,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_65])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_196,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_197,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_199,plain,
    ( ~ v1_tex_2(sK2,sK1)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_197,c_9])).

cnf(c_200,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_199])).

cnf(c_268,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_200])).

cnf(c_6,negated_conjecture,
    ( u1_struct_0(sK2) = sK3 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_270,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_6])).

cnf(c_271,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_290,plain,
    ( ~ v1_tex_2(sK2,sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_66,c_271])).

cnf(c_292,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_6])).

cnf(c_293,plain,
    ( ~ v1_tex_2(sK2,sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_327,plain,
    ( sK0(sK1,sK2) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_306,c_293])).

cnf(c_354,plain,
    ( sK0(sK1,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_327])).

cnf(c_359,plain,
    ( sK0(sK1,sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_213,plain,
    ( v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_214,plain,
    ( v1_tex_2(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_216,plain,
    ( v1_tex_2(sK2,sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_214,c_9])).

cnf(c_337,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_216,c_293])).

cnf(c_353,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_337])).

cnf(c_360,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_353])).

cnf(c_361,negated_conjecture,
    ( u1_struct_0(sK2) = sK3 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_365,plain,
    ( sK0(sK1,sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_360,c_361])).

cnf(c_366,plain,
    ( sK3 != sK3 ),
    inference(light_normalisation,[status(thm)],[c_359,c_365])).

cnf(c_367,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_366])).


%------------------------------------------------------------------------------
