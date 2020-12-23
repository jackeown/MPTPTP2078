%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:43 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 215 expanded)
%              Number of clauses        :   45 (  55 expanded)
%              Number of leaves         :   10 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  378 (1088 expanded)
%              Number of equality atoms :   29 (  29 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33,f32])).

fof(f49,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_pre_topc(X0,X1))
        & ~ v2_struct_0(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_struct_0(k1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,negated_conjecture,
    ( ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_85,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_5])).

cnf(c_86,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_85])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_511,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_86,c_11])).

cnf(c_512,plain,
    ( v2_tex_2(u1_struct_0(X0),sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_274,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_275,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v1_tdlat_3(X0)
    | ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_12,negated_conjecture,
    ( v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_277,plain,
    ( v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_14,c_12,c_11])).

cnf(c_278,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v1_tdlat_3(X0) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_516,plain,
    ( v2_struct_0(X0)
    | v2_tex_2(u1_struct_0(X0),sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_14,c_278])).

cnf(c_517,plain,
    ( v2_tex_2(u1_struct_0(X0),sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_516])).

cnf(c_637,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_517])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_pre_topc(k1_pre_topc(sK0,X0),sK0) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(X1)
    | k1_pre_topc(sK0,X0) != X1
    | u1_struct_0(X1) != sK1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_637,c_580])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,X0))
    | u1_struct_0(k1_pre_topc(sK0,X0)) != sK1 ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,X0_41))
    | u1_struct_0(k1_pre_topc(sK0,X0_41)) != sK1 ),
    inference(subtyping,[status(esa)],[c_662])).

cnf(c_837,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_808,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k1_pre_topc(sK0,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_547])).

cnf(c_833,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | ~ v2_struct_0(k1_pre_topc(sK0,X0))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_563,plain,
    ( ~ v2_struct_0(k1_pre_topc(sK0,X0))
    | v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_14])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | ~ v2_struct_0(k1_pre_topc(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_563])).

cnf(c_8,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_253,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_254,plain,
    ( v2_tex_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_258,plain,
    ( v2_tex_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_14,c_11])).

cnf(c_608,plain,
    ( v2_tex_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k1_pre_topc(sK0,X0)) ),
    inference(resolution,[status(thm)],[c_564,c_258])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k1_pre_topc(sK0,X0))
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_608])).

cnf(c_627,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_837,c_833,c_627,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.80/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.80/1.03  
% 0.80/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.80/1.03  
% 0.80/1.03  ------  iProver source info
% 0.80/1.03  
% 0.80/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.80/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.80/1.03  git: non_committed_changes: false
% 0.80/1.03  git: last_make_outside_of_git: false
% 0.80/1.03  
% 0.80/1.03  ------ 
% 0.80/1.03  
% 0.80/1.03  ------ Input Options
% 0.80/1.03  
% 0.80/1.03  --out_options                           all
% 0.80/1.03  --tptp_safe_out                         true
% 0.80/1.03  --problem_path                          ""
% 0.80/1.03  --include_path                          ""
% 0.80/1.03  --clausifier                            res/vclausify_rel
% 0.80/1.03  --clausifier_options                    --mode clausify
% 0.80/1.03  --stdin                                 false
% 0.80/1.03  --stats_out                             all
% 0.80/1.03  
% 0.80/1.03  ------ General Options
% 0.80/1.03  
% 0.80/1.03  --fof                                   false
% 0.80/1.03  --time_out_real                         305.
% 0.80/1.03  --time_out_virtual                      -1.
% 0.80/1.03  --symbol_type_check                     false
% 0.80/1.03  --clausify_out                          false
% 0.80/1.03  --sig_cnt_out                           false
% 0.80/1.03  --trig_cnt_out                          false
% 0.80/1.03  --trig_cnt_out_tolerance                1.
% 0.80/1.03  --trig_cnt_out_sk_spl                   false
% 0.80/1.03  --abstr_cl_out                          false
% 0.80/1.03  
% 0.80/1.03  ------ Global Options
% 0.80/1.03  
% 0.80/1.03  --schedule                              default
% 0.80/1.03  --add_important_lit                     false
% 0.80/1.03  --prop_solver_per_cl                    1000
% 0.80/1.03  --min_unsat_core                        false
% 0.80/1.03  --soft_assumptions                      false
% 0.80/1.03  --soft_lemma_size                       3
% 0.80/1.03  --prop_impl_unit_size                   0
% 0.80/1.03  --prop_impl_unit                        []
% 0.80/1.03  --share_sel_clauses                     true
% 0.80/1.03  --reset_solvers                         false
% 0.80/1.03  --bc_imp_inh                            [conj_cone]
% 0.80/1.03  --conj_cone_tolerance                   3.
% 0.80/1.03  --extra_neg_conj                        none
% 0.80/1.03  --large_theory_mode                     true
% 0.80/1.03  --prolific_symb_bound                   200
% 0.80/1.03  --lt_threshold                          2000
% 0.80/1.03  --clause_weak_htbl                      true
% 0.80/1.03  --gc_record_bc_elim                     false
% 0.80/1.03  
% 0.80/1.03  ------ Preprocessing Options
% 0.80/1.03  
% 0.80/1.03  --preprocessing_flag                    true
% 0.80/1.03  --time_out_prep_mult                    0.1
% 0.80/1.03  --splitting_mode                        input
% 0.80/1.03  --splitting_grd                         true
% 0.80/1.03  --splitting_cvd                         false
% 0.80/1.03  --splitting_cvd_svl                     false
% 0.80/1.03  --splitting_nvd                         32
% 0.80/1.03  --sub_typing                            true
% 0.80/1.03  --prep_gs_sim                           true
% 0.80/1.03  --prep_unflatten                        true
% 0.80/1.03  --prep_res_sim                          true
% 0.80/1.03  --prep_upred                            true
% 0.80/1.03  --prep_sem_filter                       exhaustive
% 0.80/1.03  --prep_sem_filter_out                   false
% 0.80/1.03  --pred_elim                             true
% 0.80/1.03  --res_sim_input                         true
% 0.80/1.03  --eq_ax_congr_red                       true
% 0.80/1.03  --pure_diseq_elim                       true
% 0.80/1.03  --brand_transform                       false
% 0.80/1.03  --non_eq_to_eq                          false
% 0.80/1.03  --prep_def_merge                        true
% 0.80/1.03  --prep_def_merge_prop_impl              false
% 0.80/1.03  --prep_def_merge_mbd                    true
% 0.80/1.03  --prep_def_merge_tr_red                 false
% 0.80/1.03  --prep_def_merge_tr_cl                  false
% 0.80/1.03  --smt_preprocessing                     true
% 0.80/1.03  --smt_ac_axioms                         fast
% 0.80/1.03  --preprocessed_out                      false
% 0.80/1.03  --preprocessed_stats                    false
% 0.80/1.03  
% 0.80/1.03  ------ Abstraction refinement Options
% 0.80/1.03  
% 0.80/1.03  --abstr_ref                             []
% 0.80/1.03  --abstr_ref_prep                        false
% 0.80/1.03  --abstr_ref_until_sat                   false
% 0.80/1.03  --abstr_ref_sig_restrict                funpre
% 0.80/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.80/1.03  --abstr_ref_under                       []
% 0.80/1.03  
% 0.80/1.03  ------ SAT Options
% 0.80/1.03  
% 0.80/1.03  --sat_mode                              false
% 0.80/1.03  --sat_fm_restart_options                ""
% 0.80/1.03  --sat_gr_def                            false
% 0.80/1.03  --sat_epr_types                         true
% 0.80/1.03  --sat_non_cyclic_types                  false
% 0.80/1.03  --sat_finite_models                     false
% 0.80/1.03  --sat_fm_lemmas                         false
% 0.80/1.03  --sat_fm_prep                           false
% 0.80/1.03  --sat_fm_uc_incr                        true
% 0.80/1.03  --sat_out_model                         small
% 0.80/1.03  --sat_out_clauses                       false
% 0.80/1.03  
% 0.80/1.03  ------ QBF Options
% 0.80/1.03  
% 0.80/1.03  --qbf_mode                              false
% 0.80/1.03  --qbf_elim_univ                         false
% 0.80/1.03  --qbf_dom_inst                          none
% 0.80/1.03  --qbf_dom_pre_inst                      false
% 0.80/1.03  --qbf_sk_in                             false
% 0.80/1.03  --qbf_pred_elim                         true
% 0.80/1.03  --qbf_split                             512
% 0.80/1.03  
% 0.80/1.03  ------ BMC1 Options
% 0.80/1.03  
% 0.80/1.03  --bmc1_incremental                      false
% 0.80/1.03  --bmc1_axioms                           reachable_all
% 0.80/1.03  --bmc1_min_bound                        0
% 0.80/1.03  --bmc1_max_bound                        -1
% 0.80/1.03  --bmc1_max_bound_default                -1
% 0.80/1.03  --bmc1_symbol_reachability              true
% 0.80/1.03  --bmc1_property_lemmas                  false
% 0.80/1.03  --bmc1_k_induction                      false
% 0.80/1.03  --bmc1_non_equiv_states                 false
% 0.80/1.03  --bmc1_deadlock                         false
% 0.80/1.03  --bmc1_ucm                              false
% 0.80/1.03  --bmc1_add_unsat_core                   none
% 0.80/1.03  --bmc1_unsat_core_children              false
% 0.80/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.80/1.03  --bmc1_out_stat                         full
% 0.80/1.03  --bmc1_ground_init                      false
% 0.80/1.03  --bmc1_pre_inst_next_state              false
% 0.80/1.03  --bmc1_pre_inst_state                   false
% 0.80/1.03  --bmc1_pre_inst_reach_state             false
% 0.80/1.03  --bmc1_out_unsat_core                   false
% 0.80/1.03  --bmc1_aig_witness_out                  false
% 0.80/1.03  --bmc1_verbose                          false
% 0.80/1.03  --bmc1_dump_clauses_tptp                false
% 0.80/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.80/1.03  --bmc1_dump_file                        -
% 0.80/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.80/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.80/1.03  --bmc1_ucm_extend_mode                  1
% 0.80/1.03  --bmc1_ucm_init_mode                    2
% 0.80/1.03  --bmc1_ucm_cone_mode                    none
% 0.80/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.80/1.03  --bmc1_ucm_relax_model                  4
% 0.80/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.80/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.80/1.03  --bmc1_ucm_layered_model                none
% 0.80/1.03  --bmc1_ucm_max_lemma_size               10
% 0.80/1.03  
% 0.80/1.03  ------ AIG Options
% 0.80/1.03  
% 0.80/1.03  --aig_mode                              false
% 0.80/1.03  
% 0.80/1.03  ------ Instantiation Options
% 0.80/1.03  
% 0.80/1.03  --instantiation_flag                    true
% 0.80/1.03  --inst_sos_flag                         false
% 0.80/1.03  --inst_sos_phase                        true
% 0.80/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.80/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.80/1.03  --inst_lit_sel_side                     num_symb
% 0.80/1.03  --inst_solver_per_active                1400
% 0.80/1.03  --inst_solver_calls_frac                1.
% 0.80/1.03  --inst_passive_queue_type               priority_queues
% 0.80/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.80/1.03  --inst_passive_queues_freq              [25;2]
% 0.80/1.03  --inst_dismatching                      true
% 0.80/1.03  --inst_eager_unprocessed_to_passive     true
% 0.80/1.03  --inst_prop_sim_given                   true
% 0.80/1.03  --inst_prop_sim_new                     false
% 0.80/1.03  --inst_subs_new                         false
% 0.80/1.03  --inst_eq_res_simp                      false
% 0.80/1.03  --inst_subs_given                       false
% 0.80/1.03  --inst_orphan_elimination               true
% 0.80/1.03  --inst_learning_loop_flag               true
% 0.80/1.03  --inst_learning_start                   3000
% 0.80/1.03  --inst_learning_factor                  2
% 0.80/1.03  --inst_start_prop_sim_after_learn       3
% 0.80/1.03  --inst_sel_renew                        solver
% 0.80/1.03  --inst_lit_activity_flag                true
% 0.80/1.03  --inst_restr_to_given                   false
% 0.80/1.03  --inst_activity_threshold               500
% 0.80/1.03  --inst_out_proof                        true
% 0.80/1.03  
% 0.80/1.03  ------ Resolution Options
% 0.80/1.03  
% 0.80/1.03  --resolution_flag                       true
% 0.80/1.03  --res_lit_sel                           adaptive
% 0.80/1.03  --res_lit_sel_side                      none
% 0.80/1.03  --res_ordering                          kbo
% 0.80/1.03  --res_to_prop_solver                    active
% 0.80/1.03  --res_prop_simpl_new                    false
% 0.80/1.03  --res_prop_simpl_given                  true
% 0.80/1.03  --res_passive_queue_type                priority_queues
% 0.80/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.80/1.03  --res_passive_queues_freq               [15;5]
% 0.80/1.03  --res_forward_subs                      full
% 0.80/1.03  --res_backward_subs                     full
% 0.80/1.03  --res_forward_subs_resolution           true
% 0.80/1.03  --res_backward_subs_resolution          true
% 0.80/1.03  --res_orphan_elimination                true
% 0.80/1.03  --res_time_limit                        2.
% 0.80/1.03  --res_out_proof                         true
% 0.80/1.03  
% 0.80/1.03  ------ Superposition Options
% 0.80/1.03  
% 0.80/1.03  --superposition_flag                    true
% 0.80/1.03  --sup_passive_queue_type                priority_queues
% 0.80/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.80/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.80/1.03  --demod_completeness_check              fast
% 0.80/1.03  --demod_use_ground                      true
% 0.80/1.03  --sup_to_prop_solver                    passive
% 0.80/1.03  --sup_prop_simpl_new                    true
% 0.80/1.03  --sup_prop_simpl_given                  true
% 0.80/1.03  --sup_fun_splitting                     false
% 0.80/1.03  --sup_smt_interval                      50000
% 0.80/1.03  
% 0.80/1.03  ------ Superposition Simplification Setup
% 0.80/1.03  
% 0.80/1.03  --sup_indices_passive                   []
% 0.80/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.80/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.03  --sup_full_bw                           [BwDemod]
% 0.80/1.03  --sup_immed_triv                        [TrivRules]
% 0.80/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.80/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.03  --sup_immed_bw_main                     []
% 0.80/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.80/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/1.03  
% 0.80/1.03  ------ Combination Options
% 0.80/1.03  
% 0.80/1.03  --comb_res_mult                         3
% 0.80/1.03  --comb_sup_mult                         2
% 0.80/1.03  --comb_inst_mult                        10
% 0.80/1.03  
% 0.80/1.03  ------ Debug Options
% 0.80/1.03  
% 0.80/1.03  --dbg_backtrace                         false
% 0.80/1.03  --dbg_dump_prop_clauses                 false
% 0.80/1.03  --dbg_dump_prop_clauses_file            -
% 0.80/1.03  --dbg_out_stat                          false
% 0.80/1.03  ------ Parsing...
% 0.80/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.80/1.03  
% 0.80/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.80/1.03  
% 0.80/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.80/1.03  
% 0.80/1.03  ------ Preprocessing...
% 0.80/1.03  
% 0.80/1.03  % SZS status Theorem for theBenchmark.p
% 0.80/1.03  
% 0.80/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.80/1.03  
% 0.80/1.03  fof(f9,conjecture,(
% 0.80/1.03    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.80/1.03  
% 0.80/1.03  fof(f10,negated_conjecture,(
% 0.80/1.03    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.80/1.03    inference(negated_conjecture,[],[f9])).
% 0.80/1.03  
% 0.80/1.03  fof(f29,plain,(
% 0.80/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.80/1.03    inference(ennf_transformation,[],[f10])).
% 0.80/1.03  
% 0.80/1.03  fof(f30,plain,(
% 0.80/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.80/1.03    inference(flattening,[],[f29])).
% 0.80/1.03  
% 0.80/1.03  fof(f33,plain,(
% 0.80/1.03    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.80/1.03    introduced(choice_axiom,[])).
% 0.80/1.03  
% 0.80/1.03  fof(f32,plain,(
% 0.80/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.80/1.03    introduced(choice_axiom,[])).
% 0.80/1.03  
% 0.80/1.03  fof(f34,plain,(
% 0.80/1.03    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.80/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33,f32])).
% 0.80/1.03  
% 0.80/1.03  fof(f49,plain,(
% 0.80/1.03    ~v2_tex_2(sK1,sK0)),
% 0.80/1.03    inference(cnf_transformation,[],[f34])).
% 0.80/1.03  
% 0.80/1.03  fof(f7,axiom,(
% 0.80/1.03    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.80/1.03  
% 0.80/1.03  fof(f25,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.80/1.03    inference(ennf_transformation,[],[f7])).
% 0.80/1.03  
% 0.80/1.03  fof(f26,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.80/1.03    inference(flattening,[],[f25])).
% 0.80/1.03  
% 0.80/1.03  fof(f31,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.80/1.03    inference(nnf_transformation,[],[f26])).
% 0.80/1.03  
% 0.80/1.03  fof(f42,plain,(
% 0.80/1.03    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.80/1.03    inference(cnf_transformation,[],[f31])).
% 0.80/1.03  
% 0.80/1.03  fof(f50,plain,(
% 0.80/1.03    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.80/1.03    inference(equality_resolution,[],[f42])).
% 0.80/1.03  
% 0.80/1.03  fof(f6,axiom,(
% 0.80/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.80/1.03  
% 0.80/1.03  fof(f24,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.80/1.03    inference(ennf_transformation,[],[f6])).
% 0.80/1.03  
% 0.80/1.03  fof(f40,plain,(
% 0.80/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.80/1.03    inference(cnf_transformation,[],[f24])).
% 0.80/1.03  
% 0.80/1.03  fof(f47,plain,(
% 0.80/1.03    l1_pre_topc(sK0)),
% 0.80/1.03    inference(cnf_transformation,[],[f34])).
% 0.80/1.03  
% 0.80/1.03  fof(f44,plain,(
% 0.80/1.03    ~v2_struct_0(sK0)),
% 0.80/1.03    inference(cnf_transformation,[],[f34])).
% 0.80/1.03  
% 0.80/1.03  fof(f5,axiom,(
% 0.80/1.03    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.80/1.03  
% 0.80/1.03  fof(f11,plain,(
% 0.80/1.03    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 0.80/1.03    inference(pure_predicate_removal,[],[f5])).
% 0.80/1.03  
% 0.80/1.03  fof(f12,plain,(
% 0.80/1.03    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 0.80/1.03    inference(pure_predicate_removal,[],[f11])).
% 0.80/1.03  
% 0.80/1.03  fof(f22,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.80/1.03    inference(ennf_transformation,[],[f12])).
% 0.80/1.03  
% 0.80/1.03  fof(f23,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.80/1.03    inference(flattening,[],[f22])).
% 0.80/1.03  
% 0.80/1.03  fof(f39,plain,(
% 0.80/1.03    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.80/1.03    inference(cnf_transformation,[],[f23])).
% 0.80/1.03  
% 0.80/1.03  fof(f45,plain,(
% 0.80/1.03    v2_pre_topc(sK0)),
% 0.80/1.03    inference(cnf_transformation,[],[f34])).
% 0.80/1.03  
% 0.80/1.03  fof(f46,plain,(
% 0.80/1.03    v1_tdlat_3(sK0)),
% 0.80/1.03    inference(cnf_transformation,[],[f34])).
% 0.80/1.03  
% 0.80/1.03  fof(f1,axiom,(
% 0.80/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.80/1.03  
% 0.80/1.03  fof(f14,plain,(
% 0.80/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.80/1.03    inference(pure_predicate_removal,[],[f1])).
% 0.80/1.03  
% 0.80/1.03  fof(f15,plain,(
% 0.80/1.03    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.80/1.03    inference(ennf_transformation,[],[f14])).
% 0.80/1.03  
% 0.80/1.03  fof(f16,plain,(
% 0.80/1.03    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.80/1.03    inference(flattening,[],[f15])).
% 0.80/1.03  
% 0.80/1.03  fof(f35,plain,(
% 0.80/1.03    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/1.03    inference(cnf_transformation,[],[f16])).
% 0.80/1.03  
% 0.80/1.03  fof(f3,axiom,(
% 0.80/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.80/1.03  
% 0.80/1.03  fof(f19,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.80/1.03    inference(ennf_transformation,[],[f3])).
% 0.80/1.03  
% 0.80/1.03  fof(f37,plain,(
% 0.80/1.03    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/1.03    inference(cnf_transformation,[],[f19])).
% 0.80/1.03  
% 0.80/1.03  fof(f2,axiom,(
% 0.80/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_pre_topc(X0,X1)) & ~v2_struct_0(k1_pre_topc(X0,X1))))),
% 0.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.80/1.03  
% 0.80/1.03  fof(f13,plain,(
% 0.80/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => ~v2_struct_0(k1_pre_topc(X0,X1)))),
% 0.80/1.03    inference(pure_predicate_removal,[],[f2])).
% 0.80/1.03  
% 0.80/1.03  fof(f17,plain,(
% 0.80/1.03    ! [X0,X1] : (~v2_struct_0(k1_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.80/1.03    inference(ennf_transformation,[],[f13])).
% 0.80/1.03  
% 0.80/1.03  fof(f18,plain,(
% 0.80/1.03    ! [X0,X1] : (~v2_struct_0(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.80/1.03    inference(flattening,[],[f17])).
% 0.80/1.03  
% 0.80/1.03  fof(f36,plain,(
% 0.80/1.03    ( ! [X0,X1] : (~v2_struct_0(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.80/1.03    inference(cnf_transformation,[],[f18])).
% 0.80/1.03  
% 0.80/1.03  fof(f8,axiom,(
% 0.80/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.80/1.03  
% 0.80/1.03  fof(f27,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.80/1.03    inference(ennf_transformation,[],[f8])).
% 0.80/1.03  
% 0.80/1.03  fof(f28,plain,(
% 0.80/1.03    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.80/1.03    inference(flattening,[],[f27])).
% 0.80/1.03  
% 0.80/1.03  fof(f43,plain,(
% 0.80/1.03    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.80/1.03    inference(cnf_transformation,[],[f28])).
% 0.80/1.03  
% 0.80/1.03  fof(f48,plain,(
% 0.80/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.80/1.03    inference(cnf_transformation,[],[f34])).
% 0.80/1.03  
% 0.80/1.03  cnf(c_9,negated_conjecture,
% 0.80/1.03      ( ~ v2_tex_2(sK1,sK0) ),
% 0.80/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_6,plain,
% 0.80/1.03      ( v2_tex_2(u1_struct_0(X0),X1)
% 0.80/1.03      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | ~ m1_pre_topc(X0,X1)
% 0.80/1.03      | ~ v1_tdlat_3(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | v2_struct_0(X0)
% 0.80/1.03      | ~ l1_pre_topc(X1) ),
% 0.80/1.03      inference(cnf_transformation,[],[f50]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_5,plain,
% 0.80/1.03      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | ~ m1_pre_topc(X0,X1)
% 0.80/1.03      | ~ l1_pre_topc(X1) ),
% 0.80/1.03      inference(cnf_transformation,[],[f40]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_85,plain,
% 0.80/1.03      ( v2_tex_2(u1_struct_0(X0),X1)
% 0.80/1.03      | ~ m1_pre_topc(X0,X1)
% 0.80/1.03      | ~ v1_tdlat_3(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | v2_struct_0(X0)
% 0.80/1.03      | ~ l1_pre_topc(X1) ),
% 0.80/1.03      inference(global_propositional_subsumption,[status(thm)],[c_6,c_5]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_86,plain,
% 0.80/1.03      ( v2_tex_2(u1_struct_0(X0),X1)
% 0.80/1.03      | ~ m1_pre_topc(X0,X1)
% 0.80/1.03      | ~ v1_tdlat_3(X0)
% 0.80/1.03      | v2_struct_0(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | ~ l1_pre_topc(X1) ),
% 0.80/1.03      inference(renaming,[status(thm)],[c_85]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_11,negated_conjecture,
% 0.80/1.03      ( l1_pre_topc(sK0) ),
% 0.80/1.03      inference(cnf_transformation,[],[f47]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_511,plain,
% 0.80/1.03      ( v2_tex_2(u1_struct_0(X0),X1)
% 0.80/1.03      | ~ m1_pre_topc(X0,X1)
% 0.80/1.03      | ~ v1_tdlat_3(X0)
% 0.80/1.03      | v2_struct_0(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | sK0 != X1 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_86,c_11]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_512,plain,
% 0.80/1.03      ( v2_tex_2(u1_struct_0(X0),sK0)
% 0.80/1.03      | ~ m1_pre_topc(X0,sK0)
% 0.80/1.03      | ~ v1_tdlat_3(X0)
% 0.80/1.03      | v2_struct_0(X0)
% 0.80/1.03      | v2_struct_0(sK0) ),
% 0.80/1.03      inference(unflattening,[status(thm)],[c_511]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_14,negated_conjecture,
% 0.80/1.03      ( ~ v2_struct_0(sK0) ),
% 0.80/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_4,plain,
% 0.80/1.03      ( ~ m1_pre_topc(X0,X1)
% 0.80/1.03      | ~ v1_tdlat_3(X1)
% 0.80/1.03      | v1_tdlat_3(X0)
% 0.80/1.03      | ~ v2_pre_topc(X1)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | ~ l1_pre_topc(X1) ),
% 0.80/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_13,negated_conjecture,
% 0.80/1.03      ( v2_pre_topc(sK0) ),
% 0.80/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_274,plain,
% 0.80/1.03      ( ~ m1_pre_topc(X0,X1)
% 0.80/1.03      | ~ v1_tdlat_3(X1)
% 0.80/1.03      | v1_tdlat_3(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | ~ l1_pre_topc(X1)
% 0.80/1.03      | sK0 != X1 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_275,plain,
% 0.80/1.03      ( ~ m1_pre_topc(X0,sK0)
% 0.80/1.03      | v1_tdlat_3(X0)
% 0.80/1.03      | ~ v1_tdlat_3(sK0)
% 0.80/1.03      | v2_struct_0(sK0)
% 0.80/1.03      | ~ l1_pre_topc(sK0) ),
% 0.80/1.03      inference(unflattening,[status(thm)],[c_274]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_12,negated_conjecture,
% 0.80/1.03      ( v1_tdlat_3(sK0) ),
% 0.80/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_277,plain,
% 0.80/1.03      ( v1_tdlat_3(X0) | ~ m1_pre_topc(X0,sK0) ),
% 0.80/1.03      inference(global_propositional_subsumption,
% 0.80/1.03                [status(thm)],
% 0.80/1.03                [c_275,c_14,c_12,c_11]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_278,plain,
% 0.80/1.03      ( ~ m1_pre_topc(X0,sK0) | v1_tdlat_3(X0) ),
% 0.80/1.03      inference(renaming,[status(thm)],[c_277]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_516,plain,
% 0.80/1.03      ( v2_struct_0(X0)
% 0.80/1.03      | v2_tex_2(u1_struct_0(X0),sK0)
% 0.80/1.03      | ~ m1_pre_topc(X0,sK0) ),
% 0.80/1.03      inference(global_propositional_subsumption,
% 0.80/1.03                [status(thm)],
% 0.80/1.03                [c_512,c_14,c_278]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_517,plain,
% 0.80/1.03      ( v2_tex_2(u1_struct_0(X0),sK0)
% 0.80/1.03      | ~ m1_pre_topc(X0,sK0)
% 0.80/1.03      | v2_struct_0(X0) ),
% 0.80/1.03      inference(renaming,[status(thm)],[c_516]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_637,plain,
% 0.80/1.03      ( ~ m1_pre_topc(X0,sK0)
% 0.80/1.03      | v2_struct_0(X0)
% 0.80/1.03      | u1_struct_0(X0) != sK1
% 0.80/1.03      | sK0 != sK0 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_517]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_0,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | m1_pre_topc(k1_pre_topc(X1,X0),X1)
% 0.80/1.03      | ~ l1_pre_topc(X1) ),
% 0.80/1.03      inference(cnf_transformation,[],[f35]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_579,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | m1_pre_topc(k1_pre_topc(X1,X0),X1)
% 0.80/1.03      | sK0 != X1 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_580,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | m1_pre_topc(k1_pre_topc(sK0,X0),sK0) ),
% 0.80/1.03      inference(unflattening,[status(thm)],[c_579]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_661,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | k1_pre_topc(sK0,X0) != X1
% 0.80/1.03      | u1_struct_0(X1) != sK1
% 0.80/1.03      | sK0 != sK0 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_637,c_580]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_662,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | v2_struct_0(k1_pre_topc(sK0,X0))
% 0.80/1.03      | u1_struct_0(k1_pre_topc(sK0,X0)) != sK1 ),
% 0.80/1.03      inference(unflattening,[status(thm)],[c_661]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_806,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | v2_struct_0(k1_pre_topc(sK0,X0_41))
% 0.80/1.03      | u1_struct_0(k1_pre_topc(sK0,X0_41)) != sK1 ),
% 0.80/1.03      inference(subtyping,[status(esa)],[c_662]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_837,plain,
% 0.80/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | v2_struct_0(k1_pre_topc(sK0,sK1))
% 0.80/1.03      | u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1 ),
% 0.80/1.03      inference(instantiation,[status(thm)],[c_806]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_2,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | ~ l1_pre_topc(X1)
% 0.80/1.03      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 0.80/1.03      inference(cnf_transformation,[],[f37]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_546,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | u1_struct_0(k1_pre_topc(X1,X0)) = X0
% 0.80/1.03      | sK0 != X1 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_547,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ),
% 0.80/1.03      inference(unflattening,[status(thm)],[c_546]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_808,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | u1_struct_0(k1_pre_topc(sK0,X0_41)) = X0_41 ),
% 0.80/1.03      inference(subtyping,[status(esa)],[c_547]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_833,plain,
% 0.80/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 0.80/1.03      inference(instantiation,[status(thm)],[c_808]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_1,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | v1_xboole_0(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | ~ v2_struct_0(k1_pre_topc(X1,X0))
% 0.80/1.03      | ~ l1_pre_topc(X1) ),
% 0.80/1.03      inference(cnf_transformation,[],[f36]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_558,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | v1_xboole_0(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | ~ v2_struct_0(k1_pre_topc(X1,X0))
% 0.80/1.03      | sK0 != X1 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_559,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | v1_xboole_0(X0)
% 0.80/1.03      | ~ v2_struct_0(k1_pre_topc(sK0,X0))
% 0.80/1.03      | v2_struct_0(sK0) ),
% 0.80/1.03      inference(unflattening,[status(thm)],[c_558]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_563,plain,
% 0.80/1.03      ( ~ v2_struct_0(k1_pre_topc(sK0,X0))
% 0.80/1.03      | v1_xboole_0(X0)
% 0.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.80/1.03      inference(global_propositional_subsumption,
% 0.80/1.03                [status(thm)],
% 0.80/1.03                [c_559,c_14]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_564,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | v1_xboole_0(X0)
% 0.80/1.03      | ~ v2_struct_0(k1_pre_topc(sK0,X0)) ),
% 0.80/1.03      inference(renaming,[status(thm)],[c_563]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_8,plain,
% 0.80/1.03      ( v2_tex_2(X0,X1)
% 0.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | ~ v2_pre_topc(X1)
% 0.80/1.03      | ~ v1_xboole_0(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | ~ l1_pre_topc(X1) ),
% 0.80/1.03      inference(cnf_transformation,[],[f43]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_253,plain,
% 0.80/1.03      ( v2_tex_2(X0,X1)
% 0.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.03      | ~ v1_xboole_0(X0)
% 0.80/1.03      | v2_struct_0(X1)
% 0.80/1.03      | ~ l1_pre_topc(X1)
% 0.80/1.03      | sK0 != X1 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_254,plain,
% 0.80/1.03      ( v2_tex_2(X0,sK0)
% 0.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | ~ v1_xboole_0(X0)
% 0.80/1.03      | v2_struct_0(sK0)
% 0.80/1.03      | ~ l1_pre_topc(sK0) ),
% 0.80/1.03      inference(unflattening,[status(thm)],[c_253]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_258,plain,
% 0.80/1.03      ( v2_tex_2(X0,sK0)
% 0.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | ~ v1_xboole_0(X0) ),
% 0.80/1.03      inference(global_propositional_subsumption,
% 0.80/1.03                [status(thm)],
% 0.80/1.03                [c_254,c_14,c_11]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_608,plain,
% 0.80/1.03      ( v2_tex_2(X0,sK0)
% 0.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | ~ v2_struct_0(k1_pre_topc(sK0,X0)) ),
% 0.80/1.03      inference(resolution,[status(thm)],[c_564,c_258]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_626,plain,
% 0.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | ~ v2_struct_0(k1_pre_topc(sK0,X0))
% 0.80/1.03      | sK0 != sK0
% 0.80/1.03      | sK1 != X0 ),
% 0.80/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_608]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_627,plain,
% 0.80/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.80/1.03      | ~ v2_struct_0(k1_pre_topc(sK0,sK1)) ),
% 0.80/1.03      inference(unflattening,[status(thm)],[c_626]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(c_10,negated_conjecture,
% 0.80/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.80/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.80/1.03  
% 0.80/1.03  cnf(contradiction,plain,
% 0.80/1.03      ( $false ),
% 0.80/1.03      inference(minisat,[status(thm)],[c_837,c_833,c_627,c_10]) ).
% 0.80/1.03  
% 0.80/1.03  
% 0.80/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.80/1.03  
% 0.80/1.03  ------                               Statistics
% 0.80/1.03  
% 0.80/1.03  ------ General
% 0.80/1.03  
% 0.80/1.03  abstr_ref_over_cycles:                  0
% 0.80/1.03  abstr_ref_under_cycles:                 0
% 0.80/1.03  gc_basic_clause_elim:                   0
% 0.80/1.03  forced_gc_time:                         0
% 0.80/1.03  parsing_time:                           0.01
% 0.80/1.03  unif_index_cands_time:                  0.
% 0.80/1.03  unif_index_add_time:                    0.
% 0.80/1.03  orderings_time:                         0.
% 0.80/1.03  out_proof_time:                         0.009
% 0.80/1.03  total_time:                             0.052
% 0.80/1.03  num_of_symbols:                         44
% 0.80/1.03  num_of_terms:                           596
% 0.80/1.03  
% 0.80/1.03  ------ Preprocessing
% 0.80/1.03  
% 0.80/1.03  num_of_splits:                          0
% 0.80/1.03  num_of_split_atoms:                     0
% 0.80/1.03  num_of_reused_defs:                     0
% 0.80/1.03  num_eq_ax_congr_red:                    4
% 0.80/1.03  num_of_sem_filtered_clauses:            0
% 0.80/1.03  num_of_subtypes:                        3
% 0.80/1.03  monotx_restored_types:                  0
% 0.80/1.03  sat_num_of_epr_types:                   0
% 0.80/1.03  sat_num_of_non_cyclic_types:            0
% 0.80/1.03  sat_guarded_non_collapsed_types:        1
% 0.80/1.03  num_pure_diseq_elim:                    0
% 0.80/1.03  simp_replaced_by:                       0
% 0.80/1.03  res_preprocessed:                       21
% 0.80/1.03  prep_upred:                             0
% 0.80/1.03  prep_unflattend:                        25
% 0.80/1.03  smt_new_axioms:                         0
% 0.80/1.03  pred_elim_cands:                        2
% 0.80/1.03  pred_elim:                              6
% 0.80/1.03  pred_elim_cl:                           9
% 0.80/1.03  pred_elim_cycles:                       11
% 0.80/1.03  merged_defs:                            0
% 0.80/1.03  merged_defs_ncl:                        0
% 0.80/1.03  bin_hyper_res:                          0
% 0.80/1.03  prep_cycles:                            2
% 0.80/1.03  pred_elim_time:                         0.01
% 0.80/1.03  splitting_time:                         0.
% 0.80/1.03  sem_filter_time:                        0.
% 0.80/1.03  monotx_time:                            0.
% 0.80/1.03  subtype_inf_time:                       0.
% 0.80/1.03  
% 0.80/1.03  ------ Problem properties
% 0.80/1.03  
% 0.80/1.03  clauses:                                0
% 0.80/1.03  conjectures:                            0
% 0.80/1.03  epr:                                    0
% 0.80/1.03  horn:                                   0
% 0.80/1.03  ground:                                 0
% 0.80/1.03  unary:                                  0
% 0.80/1.03  binary:                                 0
% 0.80/1.03  lits:                                   0
% 0.80/1.03  lits_eq:                                0
% 0.80/1.03  fd_pure:                                0
% 0.80/1.03  fd_pseudo:                              0
% 0.80/1.03  fd_cond:                                0
% 0.80/1.03  fd_pseudo_cond:                         0
% 0.80/1.03  ac_symbols:                             undef
% 0.80/1.03  
% 0.80/1.03  ------ Propositional Solver
% 0.80/1.03  
% 0.80/1.03  prop_solver_calls:                      10
% 0.80/1.03  prop_fast_solver_calls:                 259
% 0.80/1.03  smt_solver_calls:                       0
% 0.80/1.03  smt_fast_solver_calls:                  0
% 0.80/1.03  prop_num_of_clauses:                    183
% 0.80/1.03  prop_preprocess_simplified:             682
% 0.80/1.03  prop_fo_subsumed:                       14
% 0.80/1.03  prop_solver_time:                       0.
% 0.80/1.03  smt_solver_time:                        0.
% 0.80/1.03  smt_fast_solver_time:                   0.
% 0.80/1.03  prop_fast_solver_time:                  0.
% 0.80/1.03  prop_unsat_core_time:                   0.
% 0.80/1.03  
% 0.80/1.03  ------ QBF
% 0.80/1.03  
% 0.80/1.03  qbf_q_res:                              0
% 0.80/1.03  qbf_num_tautologies:                    0
% 0.80/1.03  qbf_prep_cycles:                        0
% 0.80/1.03  
% 0.80/1.03  ------ BMC1
% 0.80/1.03  
% 0.80/1.03  bmc1_current_bound:                     -1
% 0.80/1.03  bmc1_last_solved_bound:                 -1
% 0.80/1.03  bmc1_unsat_core_size:                   -1
% 0.80/1.03  bmc1_unsat_core_parents_size:           -1
% 0.80/1.03  bmc1_merge_next_fun:                    0
% 0.80/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.80/1.03  
% 0.80/1.03  ------ Instantiation
% 0.80/1.03  
% 0.80/1.03  inst_num_of_clauses:                    undef
% 0.80/1.03  inst_num_in_passive:                    undef
% 0.80/1.03  inst_num_in_active:                     0
% 0.80/1.03  inst_num_in_unprocessed:                0
% 0.80/1.03  inst_num_of_loops:                      0
% 0.80/1.03  inst_num_of_learning_restarts:          0
% 0.80/1.03  inst_num_moves_active_passive:          0
% 0.80/1.03  inst_lit_activity:                      0
% 0.80/1.03  inst_lit_activity_moves:                0
% 0.80/1.03  inst_num_tautologies:                   0
% 0.80/1.03  inst_num_prop_implied:                  0
% 0.80/1.03  inst_num_existing_simplified:           0
% 0.80/1.03  inst_num_eq_res_simplified:             0
% 0.80/1.03  inst_num_child_elim:                    0
% 0.80/1.03  inst_num_of_dismatching_blockings:      0
% 0.80/1.03  inst_num_of_non_proper_insts:           0
% 0.80/1.03  inst_num_of_duplicates:                 0
% 0.80/1.03  inst_inst_num_from_inst_to_res:         0
% 0.80/1.03  inst_dismatching_checking_time:         0.
% 0.80/1.03  
% 0.80/1.03  ------ Resolution
% 0.80/1.03  
% 0.80/1.03  res_num_of_clauses:                     6
% 0.80/1.03  res_num_in_passive:                     0
% 0.80/1.03  res_num_in_active:                      0
% 0.80/1.03  res_num_of_loops:                       23
% 0.80/1.03  res_forward_subset_subsumed:            2
% 0.80/1.03  res_backward_subset_subsumed:           0
% 0.80/1.03  res_forward_subsumed:                   1
% 0.80/1.03  res_backward_subsumed:                  0
% 0.80/1.03  res_forward_subsumption_resolution:     0
% 0.80/1.03  res_backward_subsumption_resolution:    0
% 0.80/1.03  res_clause_to_clause_subsumption:       12
% 0.80/1.03  res_orphan_elimination:                 0
% 0.80/1.03  res_tautology_del:                      0
% 0.80/1.03  res_num_eq_res_simplified:              0
% 0.80/1.03  res_num_sel_changes:                    0
% 0.80/1.03  res_moves_from_active_to_pass:          0
% 0.80/1.03  
% 0.80/1.03  ------ Superposition
% 0.80/1.03  
% 0.80/1.03  sup_time_total:                         0.
% 0.80/1.03  sup_time_generating:                    0.
% 0.80/1.03  sup_time_sim_full:                      0.
% 0.80/1.03  sup_time_sim_immed:                     0.
% 0.80/1.03  
% 0.80/1.03  sup_num_of_clauses:                     undef
% 0.80/1.03  sup_num_in_active:                      undef
% 0.80/1.03  sup_num_in_passive:                     undef
% 0.80/1.03  sup_num_of_loops:                       0
% 0.80/1.03  sup_fw_superposition:                   0
% 0.80/1.03  sup_bw_superposition:                   0
% 0.80/1.03  sup_immediate_simplified:               0
% 0.80/1.03  sup_given_eliminated:                   0
% 0.80/1.03  comparisons_done:                       0
% 0.80/1.03  comparisons_avoided:                    0
% 0.80/1.03  
% 0.80/1.03  ------ Simplifications
% 0.80/1.03  
% 0.80/1.03  
% 0.80/1.03  sim_fw_subset_subsumed:                 0
% 0.80/1.03  sim_bw_subset_subsumed:                 0
% 0.80/1.03  sim_fw_subsumed:                        0
% 0.80/1.03  sim_bw_subsumed:                        0
% 0.80/1.03  sim_fw_subsumption_res:                 0
% 0.80/1.03  sim_bw_subsumption_res:                 0
% 0.80/1.03  sim_tautology_del:                      0
% 0.80/1.03  sim_eq_tautology_del:                   0
% 0.80/1.03  sim_eq_res_simp:                        0
% 0.80/1.03  sim_fw_demodulated:                     0
% 0.80/1.03  sim_bw_demodulated:                     0
% 0.80/1.03  sim_light_normalised:                   0
% 0.80/1.03  sim_joinable_taut:                      0
% 0.80/1.03  sim_joinable_simp:                      0
% 0.80/1.03  sim_ac_normalised:                      0
% 0.80/1.03  sim_smt_subsumption:                    0
% 0.80/1.03  
%------------------------------------------------------------------------------
