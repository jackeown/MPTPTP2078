%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1848+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:39 EST 2020

% Result     : Theorem 0.45s
% Output     : CNFRefutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   50 (  93 expanded)
%              Number of clauses        :   22 (  25 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   17
%              Number of atoms          :  178 ( 364 expanded)
%              Number of equality atoms :   45 (  90 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f6,plain,(
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

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ~ ( v1_tex_2(X1,X0)
                & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
     => ( v1_tex_2(sK2,X0)
        & u1_struct_0(sK2) = u1_struct_0(X0)
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_tex_2(X1,X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( v1_tex_2(X1,sK1)
          & u1_struct_0(sK1) = u1_struct_0(X1)
          & m1_pre_topc(X1,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( v1_tex_2(sK2,sK1)
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & m1_pre_topc(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f18,f17])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f29,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_62,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_6])).

cnf(c_9,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_122,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_9])).

cnf(c_123,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,negated_conjecture,
    ( v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_125,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_123,c_10,c_7])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ v1_subset_1(X0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_133,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_134,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_136,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_134,c_10])).

cnf(c_169,plain,
    ( ~ v1_subset_1(X0,X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_136])).

cnf(c_170,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_186,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_125,c_170])).

cnf(c_201,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_186])).

cnf(c_206,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_201])).

cnf(c_8,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_207,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_218,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_206,c_207])).

cnf(c_219,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_218])).


%------------------------------------------------------------------------------
