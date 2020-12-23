%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1854+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:40 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 117 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    5 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 544 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_tex_2(k1_tex_2(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ ( v7_struct_0(X0)
                & v1_tex_2(k1_tex_2(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_tex_2(k1_tex_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_tex_2(k1_tex_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_tex_2(k1_tex_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( v7_struct_0(X0)
        & v1_tex_2(k1_tex_2(X0,sK1),X0)
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v7_struct_0(X0)
            & v1_tex_2(k1_tex_2(X0,X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v7_struct_0(sK0)
          & v1_tex_2(k1_tex_2(sK0,X1),sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( v7_struct_0(sK0)
    & v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).

fof(f22,plain,(
    v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_82,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_0,c_5])).

cnf(c_8,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,negated_conjecture,
    ( v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_84,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_82,c_8,c_7,c_4])).

cnf(c_85,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_84])).

cnf(c_98,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_2,c_85])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_100,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_98,c_8,c_7,c_6])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_110,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v2_struct_0(k1_tex_2(sK0,X0))
    | v2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_114,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_110,c_8])).

cnf(c_115,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v2_struct_0(k1_tex_2(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_114])).

cnf(c_130,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_100,c_115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130,c_6])).


%------------------------------------------------------------------------------
