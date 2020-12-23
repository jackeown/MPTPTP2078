%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:47 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 157 expanded)
%              Number of clauses        :   34 (  41 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  243 ( 766 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f3,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f4,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f19,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).

fof(f32,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ v3_tex_2(X2,X0) )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK0(X0),X0)
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK0(X0),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_289,plain,
    ( k5_xboole_0(X0_47,k3_xboole_0(X0_47,X0_50)) = k6_subset_1(X0_47,X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_291,plain,
    ( k5_xboole_0(X0_47,k3_xboole_0(X0_47,k2_xboole_0(X0_47,X0_51))) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_413,plain,
    ( k6_subset_1(X0_47,k2_xboole_0(X0_47,X0_51)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_289,c_291])).

cnf(c_2,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_290,plain,
    ( m1_subset_1(k6_subset_1(X0_47,X0_50),k1_zfmisc_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_344,plain,
    ( m1_subset_1(k6_subset_1(X0_47,X0_50),k1_zfmisc_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_482,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) = iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_344])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_4,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_119,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_120,plain,
    ( v2_tex_2(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_119])).

cnf(c_8,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_192,plain,
    ( v2_tex_2(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_120,c_8])).

cnf(c_193,plain,
    ( v2_tex_2(k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_195,plain,
    ( v2_tex_2(k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_193,c_11,c_10])).

cnf(c_6,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_171,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_172,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_5,plain,
    ( v3_tex_2(sK0(X0),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,negated_conjecture,
    ( ~ v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_146,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1) != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_147,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_151,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_147,c_11,c_10,c_9,c_8])).

cnf(c_176,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_172,c_11,c_10,c_8,c_151])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK1 != sK1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_176])).

cnf(c_241,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_288,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_241])).

cnf(c_345,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_488,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_482,c_345])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.88/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.88/0.99  
% 0.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.88/0.99  
% 0.88/0.99  ------  iProver source info
% 0.88/0.99  
% 0.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.88/0.99  git: non_committed_changes: false
% 0.88/0.99  git: last_make_outside_of_git: false
% 0.88/0.99  
% 0.88/0.99  ------ 
% 0.88/0.99  
% 0.88/0.99  ------ Input Options
% 0.88/0.99  
% 0.88/0.99  --out_options                           all
% 0.88/0.99  --tptp_safe_out                         true
% 0.88/0.99  --problem_path                          ""
% 0.88/0.99  --include_path                          ""
% 0.88/0.99  --clausifier                            res/vclausify_rel
% 0.88/0.99  --clausifier_options                    --mode clausify
% 0.88/0.99  --stdin                                 false
% 0.88/0.99  --stats_out                             all
% 0.88/0.99  
% 0.88/0.99  ------ General Options
% 0.88/0.99  
% 0.88/0.99  --fof                                   false
% 0.88/0.99  --time_out_real                         305.
% 0.88/0.99  --time_out_virtual                      -1.
% 0.88/0.99  --symbol_type_check                     false
% 0.88/0.99  --clausify_out                          false
% 0.88/0.99  --sig_cnt_out                           false
% 0.88/0.99  --trig_cnt_out                          false
% 0.88/0.99  --trig_cnt_out_tolerance                1.
% 0.88/0.99  --trig_cnt_out_sk_spl                   false
% 0.88/0.99  --abstr_cl_out                          false
% 0.88/0.99  
% 0.88/0.99  ------ Global Options
% 0.88/0.99  
% 0.88/0.99  --schedule                              default
% 0.88/0.99  --add_important_lit                     false
% 0.88/0.99  --prop_solver_per_cl                    1000
% 0.88/0.99  --min_unsat_core                        false
% 0.88/0.99  --soft_assumptions                      false
% 0.88/0.99  --soft_lemma_size                       3
% 0.88/0.99  --prop_impl_unit_size                   0
% 0.88/0.99  --prop_impl_unit                        []
% 0.88/0.99  --share_sel_clauses                     true
% 0.88/0.99  --reset_solvers                         false
% 0.88/0.99  --bc_imp_inh                            [conj_cone]
% 0.88/0.99  --conj_cone_tolerance                   3.
% 0.88/0.99  --extra_neg_conj                        none
% 0.88/0.99  --large_theory_mode                     true
% 0.88/0.99  --prolific_symb_bound                   200
% 0.88/0.99  --lt_threshold                          2000
% 0.88/0.99  --clause_weak_htbl                      true
% 0.88/0.99  --gc_record_bc_elim                     false
% 0.88/0.99  
% 0.88/0.99  ------ Preprocessing Options
% 0.88/0.99  
% 0.88/0.99  --preprocessing_flag                    true
% 0.88/0.99  --time_out_prep_mult                    0.1
% 0.88/0.99  --splitting_mode                        input
% 0.88/0.99  --splitting_grd                         true
% 0.88/0.99  --splitting_cvd                         false
% 0.88/0.99  --splitting_cvd_svl                     false
% 0.88/0.99  --splitting_nvd                         32
% 0.88/0.99  --sub_typing                            true
% 0.88/0.99  --prep_gs_sim                           true
% 0.88/0.99  --prep_unflatten                        true
% 0.88/0.99  --prep_res_sim                          true
% 0.88/0.99  --prep_upred                            true
% 0.88/0.99  --prep_sem_filter                       exhaustive
% 0.88/0.99  --prep_sem_filter_out                   false
% 0.88/0.99  --pred_elim                             true
% 0.88/0.99  --res_sim_input                         true
% 0.88/0.99  --eq_ax_congr_red                       true
% 0.88/0.99  --pure_diseq_elim                       true
% 0.88/0.99  --brand_transform                       false
% 0.88/0.99  --non_eq_to_eq                          false
% 0.88/0.99  --prep_def_merge                        true
% 0.88/0.99  --prep_def_merge_prop_impl              false
% 0.88/0.99  --prep_def_merge_mbd                    true
% 0.88/0.99  --prep_def_merge_tr_red                 false
% 0.88/0.99  --prep_def_merge_tr_cl                  false
% 0.88/0.99  --smt_preprocessing                     true
% 0.88/0.99  --smt_ac_axioms                         fast
% 0.88/0.99  --preprocessed_out                      false
% 0.88/0.99  --preprocessed_stats                    false
% 0.88/0.99  
% 0.88/0.99  ------ Abstraction refinement Options
% 0.88/0.99  
% 0.88/0.99  --abstr_ref                             []
% 0.88/0.99  --abstr_ref_prep                        false
% 0.88/0.99  --abstr_ref_until_sat                   false
% 0.88/0.99  --abstr_ref_sig_restrict                funpre
% 0.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/0.99  --abstr_ref_under                       []
% 0.88/0.99  
% 0.88/0.99  ------ SAT Options
% 0.88/0.99  
% 0.88/0.99  --sat_mode                              false
% 0.88/0.99  --sat_fm_restart_options                ""
% 0.88/0.99  --sat_gr_def                            false
% 0.88/0.99  --sat_epr_types                         true
% 0.88/0.99  --sat_non_cyclic_types                  false
% 0.88/0.99  --sat_finite_models                     false
% 0.88/0.99  --sat_fm_lemmas                         false
% 0.88/0.99  --sat_fm_prep                           false
% 0.88/0.99  --sat_fm_uc_incr                        true
% 0.88/0.99  --sat_out_model                         small
% 0.88/0.99  --sat_out_clauses                       false
% 0.88/0.99  
% 0.88/0.99  ------ QBF Options
% 0.88/0.99  
% 0.88/0.99  --qbf_mode                              false
% 0.88/0.99  --qbf_elim_univ                         false
% 0.88/0.99  --qbf_dom_inst                          none
% 0.88/0.99  --qbf_dom_pre_inst                      false
% 0.88/0.99  --qbf_sk_in                             false
% 0.88/0.99  --qbf_pred_elim                         true
% 0.88/0.99  --qbf_split                             512
% 0.88/0.99  
% 0.88/0.99  ------ BMC1 Options
% 0.88/0.99  
% 0.88/0.99  --bmc1_incremental                      false
% 0.88/0.99  --bmc1_axioms                           reachable_all
% 0.88/0.99  --bmc1_min_bound                        0
% 0.88/0.99  --bmc1_max_bound                        -1
% 0.88/0.99  --bmc1_max_bound_default                -1
% 0.88/0.99  --bmc1_symbol_reachability              true
% 0.88/0.99  --bmc1_property_lemmas                  false
% 0.88/0.99  --bmc1_k_induction                      false
% 0.88/0.99  --bmc1_non_equiv_states                 false
% 0.88/0.99  --bmc1_deadlock                         false
% 0.88/0.99  --bmc1_ucm                              false
% 0.88/0.99  --bmc1_add_unsat_core                   none
% 0.88/0.99  --bmc1_unsat_core_children              false
% 0.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/0.99  --bmc1_out_stat                         full
% 0.88/0.99  --bmc1_ground_init                      false
% 0.88/0.99  --bmc1_pre_inst_next_state              false
% 0.88/0.99  --bmc1_pre_inst_state                   false
% 0.88/0.99  --bmc1_pre_inst_reach_state             false
% 0.88/0.99  --bmc1_out_unsat_core                   false
% 0.88/0.99  --bmc1_aig_witness_out                  false
% 0.88/0.99  --bmc1_verbose                          false
% 0.88/0.99  --bmc1_dump_clauses_tptp                false
% 0.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.88/0.99  --bmc1_dump_file                        -
% 0.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.88/0.99  --bmc1_ucm_extend_mode                  1
% 0.88/0.99  --bmc1_ucm_init_mode                    2
% 0.88/0.99  --bmc1_ucm_cone_mode                    none
% 0.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.88/0.99  --bmc1_ucm_relax_model                  4
% 0.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/0.99  --bmc1_ucm_layered_model                none
% 0.88/0.99  --bmc1_ucm_max_lemma_size               10
% 0.88/0.99  
% 0.88/0.99  ------ AIG Options
% 0.88/0.99  
% 0.88/0.99  --aig_mode                              false
% 0.88/0.99  
% 0.88/0.99  ------ Instantiation Options
% 0.88/0.99  
% 0.88/0.99  --instantiation_flag                    true
% 0.88/0.99  --inst_sos_flag                         false
% 0.88/0.99  --inst_sos_phase                        true
% 0.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/0.99  --inst_lit_sel_side                     num_symb
% 0.88/0.99  --inst_solver_per_active                1400
% 0.88/0.99  --inst_solver_calls_frac                1.
% 0.88/0.99  --inst_passive_queue_type               priority_queues
% 0.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.88/0.99  --inst_passive_queues_freq              [25;2]
% 0.88/0.99  --inst_dismatching                      true
% 0.88/0.99  --inst_eager_unprocessed_to_passive     true
% 0.88/0.99  --inst_prop_sim_given                   true
% 0.88/0.99  --inst_prop_sim_new                     false
% 0.88/0.99  --inst_subs_new                         false
% 0.88/0.99  --inst_eq_res_simp                      false
% 0.88/0.99  --inst_subs_given                       false
% 0.88/0.99  --inst_orphan_elimination               true
% 0.88/0.99  --inst_learning_loop_flag               true
% 0.88/0.99  --inst_learning_start                   3000
% 0.88/0.99  --inst_learning_factor                  2
% 0.88/0.99  --inst_start_prop_sim_after_learn       3
% 0.88/0.99  --inst_sel_renew                        solver
% 0.88/0.99  --inst_lit_activity_flag                true
% 0.88/0.99  --inst_restr_to_given                   false
% 0.88/0.99  --inst_activity_threshold               500
% 0.88/0.99  --inst_out_proof                        true
% 0.88/0.99  
% 0.88/0.99  ------ Resolution Options
% 0.88/0.99  
% 0.88/0.99  --resolution_flag                       true
% 0.88/0.99  --res_lit_sel                           adaptive
% 0.88/0.99  --res_lit_sel_side                      none
% 0.88/0.99  --res_ordering                          kbo
% 0.88/0.99  --res_to_prop_solver                    active
% 0.88/0.99  --res_prop_simpl_new                    false
% 0.88/0.99  --res_prop_simpl_given                  true
% 0.88/0.99  --res_passive_queue_type                priority_queues
% 0.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.88/0.99  --res_passive_queues_freq               [15;5]
% 0.88/0.99  --res_forward_subs                      full
% 0.88/0.99  --res_backward_subs                     full
% 0.88/0.99  --res_forward_subs_resolution           true
% 0.88/0.99  --res_backward_subs_resolution          true
% 0.88/0.99  --res_orphan_elimination                true
% 0.88/0.99  --res_time_limit                        2.
% 0.88/0.99  --res_out_proof                         true
% 0.88/0.99  
% 0.88/0.99  ------ Superposition Options
% 0.88/0.99  
% 0.88/0.99  --superposition_flag                    true
% 0.88/0.99  --sup_passive_queue_type                priority_queues
% 0.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.88/0.99  --demod_completeness_check              fast
% 0.88/0.99  --demod_use_ground                      true
% 0.88/0.99  --sup_to_prop_solver                    passive
% 0.88/0.99  --sup_prop_simpl_new                    true
% 0.88/0.99  --sup_prop_simpl_given                  true
% 0.88/0.99  --sup_fun_splitting                     false
% 0.88/0.99  --sup_smt_interval                      50000
% 0.88/0.99  
% 0.88/0.99  ------ Superposition Simplification Setup
% 0.88/0.99  
% 0.88/0.99  --sup_indices_passive                   []
% 0.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.99  --sup_full_bw                           [BwDemod]
% 0.88/0.99  --sup_immed_triv                        [TrivRules]
% 0.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.99  --sup_immed_bw_main                     []
% 0.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.99  
% 0.88/0.99  ------ Combination Options
% 0.88/0.99  
% 0.88/0.99  --comb_res_mult                         3
% 0.88/0.99  --comb_sup_mult                         2
% 0.88/0.99  --comb_inst_mult                        10
% 0.88/0.99  
% 0.88/0.99  ------ Debug Options
% 0.88/0.99  
% 0.88/0.99  --dbg_backtrace                         false
% 0.88/0.99  --dbg_dump_prop_clauses                 false
% 0.88/0.99  --dbg_dump_prop_clauses_file            -
% 0.88/0.99  --dbg_out_stat                          false
% 0.88/0.99  ------ Parsing...
% 0.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.88/0.99  
% 0.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.88/0.99  
% 0.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.88/0.99  
% 0.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.88/0.99  ------ Proving...
% 0.88/0.99  ------ Problem Properties 
% 0.88/0.99  
% 0.88/0.99  
% 0.88/0.99  clauses                                 4
% 0.88/0.99  conjectures                             0
% 0.88/0.99  EPR                                     0
% 0.88/0.99  Horn                                    4
% 0.88/0.99  unary                                   4
% 0.88/0.99  binary                                  0
% 0.88/0.99  lits                                    4
% 0.88/0.99  lits eq                                 2
% 0.88/0.99  fd_pure                                 0
% 0.88/0.99  fd_pseudo                               0
% 0.88/0.99  fd_cond                                 0
% 0.88/0.99  fd_pseudo_cond                          0
% 0.88/0.99  AC symbols                              0
% 0.88/0.99  
% 0.88/0.99  ------ Schedule dynamic 5 is on 
% 0.88/0.99  
% 0.88/0.99  ------ no conjectures: strip conj schedule 
% 0.88/0.99  
% 0.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.88/0.99  
% 0.88/0.99  
% 0.88/0.99  ------ 
% 0.88/0.99  Current options:
% 0.88/0.99  ------ 
% 0.88/0.99  
% 0.88/0.99  ------ Input Options
% 0.88/0.99  
% 0.88/0.99  --out_options                           all
% 0.88/0.99  --tptp_safe_out                         true
% 0.88/0.99  --problem_path                          ""
% 0.88/0.99  --include_path                          ""
% 0.88/0.99  --clausifier                            res/vclausify_rel
% 0.88/0.99  --clausifier_options                    --mode clausify
% 0.88/0.99  --stdin                                 false
% 0.88/0.99  --stats_out                             all
% 0.88/0.99  
% 0.88/0.99  ------ General Options
% 0.88/0.99  
% 0.88/0.99  --fof                                   false
% 0.88/0.99  --time_out_real                         305.
% 0.88/0.99  --time_out_virtual                      -1.
% 0.88/0.99  --symbol_type_check                     false
% 0.88/0.99  --clausify_out                          false
% 0.88/0.99  --sig_cnt_out                           false
% 0.88/0.99  --trig_cnt_out                          false
% 0.88/0.99  --trig_cnt_out_tolerance                1.
% 0.88/0.99  --trig_cnt_out_sk_spl                   false
% 0.88/0.99  --abstr_cl_out                          false
% 0.88/0.99  
% 0.88/0.99  ------ Global Options
% 0.88/0.99  
% 0.88/0.99  --schedule                              default
% 0.88/0.99  --add_important_lit                     false
% 0.88/0.99  --prop_solver_per_cl                    1000
% 0.88/0.99  --min_unsat_core                        false
% 0.88/0.99  --soft_assumptions                      false
% 0.88/0.99  --soft_lemma_size                       3
% 0.88/0.99  --prop_impl_unit_size                   0
% 0.88/0.99  --prop_impl_unit                        []
% 0.88/0.99  --share_sel_clauses                     true
% 0.88/0.99  --reset_solvers                         false
% 0.88/0.99  --bc_imp_inh                            [conj_cone]
% 0.88/0.99  --conj_cone_tolerance                   3.
% 0.88/0.99  --extra_neg_conj                        none
% 0.88/0.99  --large_theory_mode                     true
% 0.88/0.99  --prolific_symb_bound                   200
% 0.88/0.99  --lt_threshold                          2000
% 0.88/0.99  --clause_weak_htbl                      true
% 0.88/0.99  --gc_record_bc_elim                     false
% 0.88/0.99  
% 0.88/0.99  ------ Preprocessing Options
% 0.88/0.99  
% 0.88/0.99  --preprocessing_flag                    true
% 0.88/0.99  --time_out_prep_mult                    0.1
% 0.88/0.99  --splitting_mode                        input
% 0.88/0.99  --splitting_grd                         true
% 0.88/0.99  --splitting_cvd                         false
% 0.88/0.99  --splitting_cvd_svl                     false
% 0.88/0.99  --splitting_nvd                         32
% 0.88/0.99  --sub_typing                            true
% 0.88/0.99  --prep_gs_sim                           true
% 0.88/0.99  --prep_unflatten                        true
% 0.88/0.99  --prep_res_sim                          true
% 0.88/0.99  --prep_upred                            true
% 0.88/0.99  --prep_sem_filter                       exhaustive
% 0.88/0.99  --prep_sem_filter_out                   false
% 0.88/0.99  --pred_elim                             true
% 0.88/0.99  --res_sim_input                         true
% 0.88/0.99  --eq_ax_congr_red                       true
% 0.88/0.99  --pure_diseq_elim                       true
% 0.88/0.99  --brand_transform                       false
% 0.88/0.99  --non_eq_to_eq                          false
% 0.88/0.99  --prep_def_merge                        true
% 0.88/0.99  --prep_def_merge_prop_impl              false
% 0.88/0.99  --prep_def_merge_mbd                    true
% 0.88/0.99  --prep_def_merge_tr_red                 false
% 0.88/0.99  --prep_def_merge_tr_cl                  false
% 0.88/0.99  --smt_preprocessing                     true
% 0.88/0.99  --smt_ac_axioms                         fast
% 0.88/0.99  --preprocessed_out                      false
% 0.88/0.99  --preprocessed_stats                    false
% 0.88/0.99  
% 0.88/0.99  ------ Abstraction refinement Options
% 0.88/0.99  
% 0.88/0.99  --abstr_ref                             []
% 0.88/0.99  --abstr_ref_prep                        false
% 0.88/0.99  --abstr_ref_until_sat                   false
% 0.88/0.99  --abstr_ref_sig_restrict                funpre
% 0.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/0.99  --abstr_ref_under                       []
% 0.88/0.99  
% 0.88/0.99  ------ SAT Options
% 0.88/0.99  
% 0.88/0.99  --sat_mode                              false
% 0.88/0.99  --sat_fm_restart_options                ""
% 0.88/0.99  --sat_gr_def                            false
% 0.88/0.99  --sat_epr_types                         true
% 0.88/0.99  --sat_non_cyclic_types                  false
% 0.88/0.99  --sat_finite_models                     false
% 0.88/0.99  --sat_fm_lemmas                         false
% 0.88/0.99  --sat_fm_prep                           false
% 0.88/0.99  --sat_fm_uc_incr                        true
% 0.88/0.99  --sat_out_model                         small
% 0.88/0.99  --sat_out_clauses                       false
% 0.88/0.99  
% 0.88/0.99  ------ QBF Options
% 0.88/0.99  
% 0.88/0.99  --qbf_mode                              false
% 0.88/0.99  --qbf_elim_univ                         false
% 0.88/0.99  --qbf_dom_inst                          none
% 0.88/0.99  --qbf_dom_pre_inst                      false
% 0.88/0.99  --qbf_sk_in                             false
% 0.88/0.99  --qbf_pred_elim                         true
% 0.88/0.99  --qbf_split                             512
% 0.88/0.99  
% 0.88/0.99  ------ BMC1 Options
% 0.88/0.99  
% 0.88/0.99  --bmc1_incremental                      false
% 0.88/0.99  --bmc1_axioms                           reachable_all
% 0.88/0.99  --bmc1_min_bound                        0
% 0.88/0.99  --bmc1_max_bound                        -1
% 0.88/0.99  --bmc1_max_bound_default                -1
% 0.88/0.99  --bmc1_symbol_reachability              true
% 0.88/0.99  --bmc1_property_lemmas                  false
% 0.88/0.99  --bmc1_k_induction                      false
% 0.88/0.99  --bmc1_non_equiv_states                 false
% 0.88/0.99  --bmc1_deadlock                         false
% 0.88/0.99  --bmc1_ucm                              false
% 0.88/0.99  --bmc1_add_unsat_core                   none
% 0.88/0.99  --bmc1_unsat_core_children              false
% 0.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/0.99  --bmc1_out_stat                         full
% 0.88/0.99  --bmc1_ground_init                      false
% 0.88/0.99  --bmc1_pre_inst_next_state              false
% 0.88/0.99  --bmc1_pre_inst_state                   false
% 0.88/0.99  --bmc1_pre_inst_reach_state             false
% 0.88/0.99  --bmc1_out_unsat_core                   false
% 0.88/0.99  --bmc1_aig_witness_out                  false
% 0.88/0.99  --bmc1_verbose                          false
% 0.88/0.99  --bmc1_dump_clauses_tptp                false
% 0.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.88/0.99  --bmc1_dump_file                        -
% 0.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.88/0.99  --bmc1_ucm_extend_mode                  1
% 0.88/0.99  --bmc1_ucm_init_mode                    2
% 0.88/0.99  --bmc1_ucm_cone_mode                    none
% 0.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.88/0.99  --bmc1_ucm_relax_model                  4
% 0.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/0.99  --bmc1_ucm_layered_model                none
% 0.88/0.99  --bmc1_ucm_max_lemma_size               10
% 0.88/0.99  
% 0.88/0.99  ------ AIG Options
% 0.88/0.99  
% 0.88/0.99  --aig_mode                              false
% 0.88/0.99  
% 0.88/0.99  ------ Instantiation Options
% 0.88/0.99  
% 0.88/0.99  --instantiation_flag                    true
% 0.88/0.99  --inst_sos_flag                         false
% 0.88/0.99  --inst_sos_phase                        true
% 0.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/0.99  --inst_lit_sel_side                     none
% 0.88/0.99  --inst_solver_per_active                1400
% 0.88/0.99  --inst_solver_calls_frac                1.
% 0.88/0.99  --inst_passive_queue_type               priority_queues
% 0.88/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.88/0.99  --inst_passive_queues_freq              [25;2]
% 0.88/0.99  --inst_dismatching                      true
% 0.88/0.99  --inst_eager_unprocessed_to_passive     true
% 0.88/0.99  --inst_prop_sim_given                   true
% 0.88/0.99  --inst_prop_sim_new                     false
% 0.88/0.99  --inst_subs_new                         false
% 0.88/0.99  --inst_eq_res_simp                      false
% 0.88/0.99  --inst_subs_given                       false
% 0.88/0.99  --inst_orphan_elimination               true
% 0.88/0.99  --inst_learning_loop_flag               true
% 0.88/0.99  --inst_learning_start                   3000
% 0.88/0.99  --inst_learning_factor                  2
% 0.88/0.99  --inst_start_prop_sim_after_learn       3
% 0.88/0.99  --inst_sel_renew                        solver
% 0.88/0.99  --inst_lit_activity_flag                true
% 0.88/0.99  --inst_restr_to_given                   false
% 0.88/0.99  --inst_activity_threshold               500
% 0.88/0.99  --inst_out_proof                        true
% 0.88/0.99  
% 0.88/0.99  ------ Resolution Options
% 0.88/0.99  
% 0.88/0.99  --resolution_flag                       false
% 0.88/0.99  --res_lit_sel                           adaptive
% 0.88/0.99  --res_lit_sel_side                      none
% 0.88/1.00  --res_ordering                          kbo
% 0.88/1.00  --res_to_prop_solver                    active
% 0.88/1.00  --res_prop_simpl_new                    false
% 0.88/1.00  --res_prop_simpl_given                  true
% 0.88/1.00  --res_passive_queue_type                priority_queues
% 0.88/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.88/1.00  --res_passive_queues_freq               [15;5]
% 0.88/1.00  --res_forward_subs                      full
% 0.88/1.00  --res_backward_subs                     full
% 0.88/1.00  --res_forward_subs_resolution           true
% 0.88/1.00  --res_backward_subs_resolution          true
% 0.88/1.00  --res_orphan_elimination                true
% 0.88/1.00  --res_time_limit                        2.
% 0.88/1.00  --res_out_proof                         true
% 0.88/1.00  
% 0.88/1.00  ------ Superposition Options
% 0.88/1.00  
% 0.88/1.00  --superposition_flag                    true
% 0.88/1.00  --sup_passive_queue_type                priority_queues
% 0.88/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.88/1.00  --demod_completeness_check              fast
% 0.88/1.00  --demod_use_ground                      true
% 0.88/1.00  --sup_to_prop_solver                    passive
% 0.88/1.00  --sup_prop_simpl_new                    true
% 0.88/1.00  --sup_prop_simpl_given                  true
% 0.88/1.00  --sup_fun_splitting                     false
% 0.88/1.00  --sup_smt_interval                      50000
% 0.88/1.00  
% 0.88/1.00  ------ Superposition Simplification Setup
% 0.88/1.00  
% 0.88/1.00  --sup_indices_passive                   []
% 0.88/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.00  --sup_full_bw                           [BwDemod]
% 0.88/1.00  --sup_immed_triv                        [TrivRules]
% 0.88/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.00  --sup_immed_bw_main                     []
% 0.88/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.00  
% 0.88/1.00  ------ Combination Options
% 0.88/1.00  
% 0.88/1.00  --comb_res_mult                         3
% 0.88/1.00  --comb_sup_mult                         2
% 0.88/1.00  --comb_inst_mult                        10
% 0.88/1.00  
% 0.88/1.00  ------ Debug Options
% 0.88/1.00  
% 0.88/1.00  --dbg_backtrace                         false
% 0.88/1.00  --dbg_dump_prop_clauses                 false
% 0.88/1.00  --dbg_dump_prop_clauses_file            -
% 0.88/1.00  --dbg_out_stat                          false
% 0.88/1.00  
% 0.88/1.00  
% 0.88/1.00  
% 0.88/1.00  
% 0.88/1.00  ------ Proving...
% 0.88/1.00  
% 0.88/1.00  
% 0.88/1.00  % SZS status Theorem for theBenchmark.p
% 0.88/1.00  
% 0.88/1.00   Resolution empty clause
% 0.88/1.00  
% 0.88/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.88/1.00  
% 0.88/1.00  fof(f5,axiom,(
% 0.88/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.00  
% 0.88/1.00  fof(f25,plain,(
% 0.88/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.88/1.00    inference(cnf_transformation,[],[f5])).
% 0.88/1.00  
% 0.88/1.00  fof(f2,axiom,(
% 0.88/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.00  
% 0.88/1.00  fof(f22,plain,(
% 0.88/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.88/1.00    inference(cnf_transformation,[],[f2])).
% 0.88/1.00  
% 0.88/1.00  fof(f35,plain,(
% 0.88/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 0.88/1.00    inference(definition_unfolding,[],[f25,f22])).
% 0.88/1.00  
% 0.88/1.00  fof(f3,axiom,(
% 0.88/1.00    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.00  
% 0.88/1.00  fof(f23,plain,(
% 0.88/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.88/1.00    inference(cnf_transformation,[],[f3])).
% 0.88/1.00  
% 0.88/1.00  fof(f34,plain,(
% 0.88/1.00    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 0.88/1.00    inference(definition_unfolding,[],[f23,f22])).
% 0.88/1.00  
% 0.88/1.00  fof(f4,axiom,(
% 0.88/1.00    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.00  
% 0.88/1.00  fof(f24,plain,(
% 0.88/1.00    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.88/1.00    inference(cnf_transformation,[],[f4])).
% 0.88/1.00  
% 0.88/1.00  fof(f1,axiom,(
% 0.88/1.00    v1_xboole_0(k1_xboole_0)),
% 0.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.00  
% 0.88/1.00  fof(f21,plain,(
% 0.88/1.00    v1_xboole_0(k1_xboole_0)),
% 0.88/1.00    inference(cnf_transformation,[],[f1])).
% 0.88/1.00  
% 0.88/1.00  fof(f6,axiom,(
% 0.88/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.00  
% 0.88/1.00  fof(f11,plain,(
% 0.88/1.00    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.88/1.00    inference(ennf_transformation,[],[f6])).
% 0.88/1.00  
% 0.88/1.00  fof(f12,plain,(
% 0.88/1.00    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.88/1.00    inference(flattening,[],[f11])).
% 0.88/1.00  
% 0.88/1.00  fof(f26,plain,(
% 0.88/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.88/1.00    inference(cnf_transformation,[],[f12])).
% 0.88/1.00  
% 0.88/1.00  fof(f8,conjecture,(
% 0.88/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.00  
% 0.88/1.00  fof(f9,negated_conjecture,(
% 0.88/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.88/1.00    inference(negated_conjecture,[],[f8])).
% 0.88/1.00  
% 0.88/1.00  fof(f15,plain,(
% 0.88/1.00    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.88/1.00    inference(ennf_transformation,[],[f9])).
% 0.88/1.00  
% 0.88/1.00  fof(f16,plain,(
% 0.88/1.00    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.88/1.00    inference(flattening,[],[f15])).
% 0.88/1.00  
% 0.88/1.00  fof(f19,plain,(
% 0.88/1.00    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.88/1.00    introduced(choice_axiom,[])).
% 0.88/1.00  
% 0.88/1.00  fof(f20,plain,(
% 0.88/1.00    ! [X1] : (~v3_tex_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).
% 0.88/1.00  
% 0.88/1.00  fof(f32,plain,(
% 0.88/1.00    l1_pre_topc(sK1)),
% 0.88/1.00    inference(cnf_transformation,[],[f20])).
% 0.88/1.00  
% 0.88/1.00  fof(f29,plain,(
% 0.88/1.00    ~v2_struct_0(sK1)),
% 0.88/1.00    inference(cnf_transformation,[],[f20])).
% 0.88/1.00  
% 0.88/1.00  fof(f30,plain,(
% 0.88/1.00    v2_pre_topc(sK1)),
% 0.88/1.00    inference(cnf_transformation,[],[f20])).
% 0.88/1.00  
% 0.88/1.00  fof(f7,axiom,(
% 0.88/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.00  
% 0.88/1.00  fof(f10,plain,(
% 0.88/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~v3_tex_2(X2,X0)) & v2_tex_2(X1,X0))))),
% 0.88/1.00    inference(pure_predicate_removal,[],[f7])).
% 0.88/1.00  
% 0.88/1.00  fof(f13,plain,(
% 0.88/1.00    ! [X0] : (! [X1] : ((? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.88/1.00    inference(ennf_transformation,[],[f10])).
% 0.88/1.00  
% 0.88/1.00  fof(f14,plain,(
% 0.88/1.00    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.88/1.00    inference(flattening,[],[f13])).
% 0.88/1.00  
% 0.88/1.00  fof(f17,plain,(
% 0.88/1.00    ! [X0] : (? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.88/1.00    introduced(choice_axiom,[])).
% 0.88/1.00  
% 0.88/1.00  fof(f18,plain,(
% 0.88/1.00    ! [X0] : (! [X1] : ((v3_tex_2(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f17])).
% 0.88/1.00  
% 0.88/1.00  fof(f27,plain,(
% 0.88/1.00    ( ! [X0,X1] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.88/1.00    inference(cnf_transformation,[],[f18])).
% 0.88/1.00  
% 0.88/1.00  fof(f31,plain,(
% 0.88/1.00    v3_tdlat_3(sK1)),
% 0.88/1.00    inference(cnf_transformation,[],[f20])).
% 0.88/1.00  
% 0.88/1.00  fof(f28,plain,(
% 0.88/1.00    ( ! [X0,X1] : (v3_tex_2(sK0(X0),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.88/1.00    inference(cnf_transformation,[],[f18])).
% 0.88/1.00  
% 0.88/1.00  fof(f33,plain,(
% 0.88/1.00    ( ! [X1] : (~v3_tex_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.88/1.00    inference(cnf_transformation,[],[f20])).
% 0.88/1.00  
% 0.88/1.00  cnf(c_3,plain,
% 0.88/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
% 0.88/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_289,plain,
% 0.88/1.00      ( k5_xboole_0(X0_47,k3_xboole_0(X0_47,X0_50)) = k6_subset_1(X0_47,X0_50) ),
% 0.88/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_1,plain,
% 0.88/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 0.88/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_291,plain,
% 0.88/1.00      ( k5_xboole_0(X0_47,k3_xboole_0(X0_47,k2_xboole_0(X0_47,X0_51))) = k1_xboole_0 ),
% 0.88/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_413,plain,
% 0.88/1.00      ( k6_subset_1(X0_47,k2_xboole_0(X0_47,X0_51)) = k1_xboole_0 ),
% 0.88/1.00      inference(superposition,[status(thm)],[c_289,c_291]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_2,plain,
% 0.88/1.00      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 0.88/1.00      inference(cnf_transformation,[],[f24]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_290,plain,
% 0.88/1.00      ( m1_subset_1(k6_subset_1(X0_47,X0_50),k1_zfmisc_1(X0_47)) ),
% 0.88/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_344,plain,
% 0.88/1.00      ( m1_subset_1(k6_subset_1(X0_47,X0_50),k1_zfmisc_1(X0_47)) = iProver_top ),
% 0.88/1.00      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_482,plain,
% 0.88/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) = iProver_top ),
% 0.88/1.00      inference(superposition,[status(thm)],[c_413,c_344]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_0,plain,
% 0.88/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 0.88/1.00      inference(cnf_transformation,[],[f21]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_4,plain,
% 0.88/1.00      ( v2_tex_2(X0,X1)
% 0.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.00      | v2_struct_0(X1)
% 0.88/1.00      | ~ v2_pre_topc(X1)
% 0.88/1.00      | ~ l1_pre_topc(X1)
% 0.88/1.00      | ~ v1_xboole_0(X0) ),
% 0.88/1.00      inference(cnf_transformation,[],[f26]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_119,plain,
% 0.88/1.00      ( v2_tex_2(X0,X1)
% 0.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.00      | v2_struct_0(X1)
% 0.88/1.00      | ~ v2_pre_topc(X1)
% 0.88/1.00      | ~ l1_pre_topc(X1)
% 0.88/1.00      | k1_xboole_0 != X0 ),
% 0.88/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_120,plain,
% 0.88/1.00      ( v2_tex_2(k1_xboole_0,X0)
% 0.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 0.88/1.00      | v2_struct_0(X0)
% 0.88/1.00      | ~ v2_pre_topc(X0)
% 0.88/1.00      | ~ l1_pre_topc(X0) ),
% 0.88/1.00      inference(unflattening,[status(thm)],[c_119]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_8,negated_conjecture,
% 0.88/1.00      ( l1_pre_topc(sK1) ),
% 0.88/1.00      inference(cnf_transformation,[],[f32]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_192,plain,
% 0.88/1.00      ( v2_tex_2(k1_xboole_0,X0)
% 0.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 0.88/1.00      | v2_struct_0(X0)
% 0.88/1.00      | ~ v2_pre_topc(X0)
% 0.88/1.00      | sK1 != X0 ),
% 0.88/1.00      inference(resolution_lifted,[status(thm)],[c_120,c_8]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_193,plain,
% 0.88/1.00      ( v2_tex_2(k1_xboole_0,sK1)
% 0.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | v2_struct_0(sK1)
% 0.88/1.00      | ~ v2_pre_topc(sK1) ),
% 0.88/1.00      inference(unflattening,[status(thm)],[c_192]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_11,negated_conjecture,
% 0.88/1.00      ( ~ v2_struct_0(sK1) ),
% 0.88/1.00      inference(cnf_transformation,[],[f29]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_10,negated_conjecture,
% 0.88/1.00      ( v2_pre_topc(sK1) ),
% 0.88/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_195,plain,
% 0.88/1.00      ( v2_tex_2(k1_xboole_0,sK1)
% 0.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.00      inference(global_propositional_subsumption,
% 0.88/1.00                [status(thm)],
% 0.88/1.00                [c_193,c_11,c_10]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_6,plain,
% 0.88/1.00      ( ~ v2_tex_2(X0,X1)
% 0.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.00      | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.00      | ~ v3_tdlat_3(X1)
% 0.88/1.00      | v2_struct_0(X1)
% 0.88/1.00      | ~ v2_pre_topc(X1)
% 0.88/1.00      | ~ l1_pre_topc(X1) ),
% 0.88/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_9,negated_conjecture,
% 0.88/1.00      ( v3_tdlat_3(sK1) ),
% 0.88/1.00      inference(cnf_transformation,[],[f31]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_171,plain,
% 0.88/1.00      ( ~ v2_tex_2(X0,X1)
% 0.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.00      | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.00      | v2_struct_0(X1)
% 0.88/1.00      | ~ v2_pre_topc(X1)
% 0.88/1.00      | ~ l1_pre_topc(X1)
% 0.88/1.00      | sK1 != X1 ),
% 0.88/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_172,plain,
% 0.88/1.00      ( ~ v2_tex_2(X0,sK1)
% 0.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | v2_struct_0(sK1)
% 0.88/1.00      | ~ v2_pre_topc(sK1)
% 0.88/1.00      | ~ l1_pre_topc(sK1) ),
% 0.88/1.00      inference(unflattening,[status(thm)],[c_171]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_5,plain,
% 0.88/1.00      ( v3_tex_2(sK0(X0),X0)
% 0.88/1.00      | ~ v2_tex_2(X1,X0)
% 0.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.88/1.00      | ~ v3_tdlat_3(X0)
% 0.88/1.00      | v2_struct_0(X0)
% 0.88/1.00      | ~ v2_pre_topc(X0)
% 0.88/1.00      | ~ l1_pre_topc(X0) ),
% 0.88/1.00      inference(cnf_transformation,[],[f28]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_7,negated_conjecture,
% 0.88/1.00      ( ~ v3_tex_2(X0,sK1) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.00      inference(cnf_transformation,[],[f33]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_146,plain,
% 0.88/1.00      ( ~ v2_tex_2(X0,X1)
% 0.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | ~ v3_tdlat_3(X1)
% 0.88/1.00      | v2_struct_0(X1)
% 0.88/1.00      | ~ v2_pre_topc(X1)
% 0.88/1.00      | ~ l1_pre_topc(X1)
% 0.88/1.00      | sK0(X1) != X2
% 0.88/1.00      | sK1 != X1 ),
% 0.88/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_147,plain,
% 0.88/1.00      ( ~ v2_tex_2(X0,sK1)
% 0.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | ~ v3_tdlat_3(sK1)
% 0.88/1.00      | v2_struct_0(sK1)
% 0.88/1.00      | ~ v2_pre_topc(sK1)
% 0.88/1.00      | ~ l1_pre_topc(sK1) ),
% 0.88/1.00      inference(unflattening,[status(thm)],[c_146]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_151,plain,
% 0.88/1.00      ( ~ v2_tex_2(X0,sK1)
% 0.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.00      inference(global_propositional_subsumption,
% 0.88/1.00                [status(thm)],
% 0.88/1.00                [c_147,c_11,c_10,c_9,c_8]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_176,plain,
% 0.88/1.00      ( ~ v2_tex_2(X0,sK1) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.00      inference(global_propositional_subsumption,
% 0.88/1.00                [status(thm)],
% 0.88/1.00                [c_172,c_11,c_10,c_8,c_151]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_240,plain,
% 0.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.00      | sK1 != sK1
% 0.88/1.00      | k1_xboole_0 != X0 ),
% 0.88/1.00      inference(resolution_lifted,[status(thm)],[c_195,c_176]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_241,plain,
% 0.88/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.00      inference(unflattening,[status(thm)],[c_240]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_288,plain,
% 0.88/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.00      inference(subtyping,[status(esa)],[c_241]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_345,plain,
% 0.88/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 0.88/1.00      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 0.88/1.00  
% 0.88/1.00  cnf(c_488,plain,
% 0.88/1.00      ( $false ),
% 0.88/1.00      inference(superposition,[status(thm)],[c_482,c_345]) ).
% 0.88/1.00  
% 0.88/1.00  
% 0.88/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.88/1.00  
% 0.88/1.00  ------                               Statistics
% 0.88/1.00  
% 0.88/1.00  ------ General
% 0.88/1.00  
% 0.88/1.00  abstr_ref_over_cycles:                  0
% 0.88/1.00  abstr_ref_under_cycles:                 0
% 0.88/1.00  gc_basic_clause_elim:                   0
% 0.88/1.00  forced_gc_time:                         0
% 0.88/1.00  parsing_time:                           0.014
% 0.88/1.00  unif_index_cands_time:                  0.
% 0.88/1.00  unif_index_add_time:                    0.
% 0.88/1.00  orderings_time:                         0.
% 0.88/1.00  out_proof_time:                         0.011
% 0.88/1.00  total_time:                             0.058
% 0.88/1.00  num_of_symbols:                         52
% 0.88/1.00  num_of_terms:                           596
% 0.88/1.00  
% 0.88/1.00  ------ Preprocessing
% 0.88/1.00  
% 0.88/1.00  num_of_splits:                          0
% 0.88/1.00  num_of_split_atoms:                     0
% 0.88/1.00  num_of_reused_defs:                     0
% 0.88/1.00  num_eq_ax_congr_red:                    26
% 0.88/1.00  num_of_sem_filtered_clauses:            1
% 0.88/1.00  num_of_subtypes:                        7
% 0.88/1.00  monotx_restored_types:                  0
% 0.88/1.00  sat_num_of_epr_types:                   0
% 0.88/1.00  sat_num_of_non_cyclic_types:            0
% 0.88/1.00  sat_guarded_non_collapsed_types:        0
% 0.88/1.00  num_pure_diseq_elim:                    0
% 0.88/1.00  simp_replaced_by:                       0
% 0.88/1.00  res_preprocessed:                       31
% 0.88/1.00  prep_upred:                             0
% 0.88/1.00  prep_unflattend:                        7
% 0.88/1.00  smt_new_axioms:                         0
% 0.88/1.00  pred_elim_cands:                        1
% 0.88/1.00  pred_elim:                              7
% 0.88/1.00  pred_elim_cl:                           8
% 0.88/1.00  pred_elim_cycles:                       10
% 0.88/1.00  merged_defs:                            0
% 0.88/1.00  merged_defs_ncl:                        0
% 0.88/1.00  bin_hyper_res:                          0
% 0.88/1.00  prep_cycles:                            4
% 0.88/1.00  pred_elim_time:                         0.004
% 0.88/1.00  splitting_time:                         0.
% 0.88/1.00  sem_filter_time:                        0.
% 0.88/1.00  monotx_time:                            0.
% 0.88/1.00  subtype_inf_time:                       0.
% 0.88/1.00  
% 0.88/1.00  ------ Problem properties
% 0.88/1.00  
% 0.88/1.00  clauses:                                4
% 0.88/1.00  conjectures:                            0
% 0.88/1.00  epr:                                    0
% 0.88/1.00  horn:                                   4
% 0.88/1.00  ground:                                 1
% 0.88/1.00  unary:                                  4
% 0.88/1.00  binary:                                 0
% 0.88/1.00  lits:                                   4
% 0.88/1.00  lits_eq:                                2
% 0.88/1.00  fd_pure:                                0
% 0.88/1.00  fd_pseudo:                              0
% 0.88/1.00  fd_cond:                                0
% 0.88/1.00  fd_pseudo_cond:                         0
% 0.88/1.00  ac_symbols:                             0
% 0.88/1.00  
% 0.88/1.00  ------ Propositional Solver
% 0.88/1.00  
% 0.88/1.00  prop_solver_calls:                      26
% 0.88/1.00  prop_fast_solver_calls:                 159
% 0.88/1.00  smt_solver_calls:                       0
% 0.88/1.00  smt_fast_solver_calls:                  0
% 0.88/1.00  prop_num_of_clauses:                    163
% 0.88/1.00  prop_preprocess_simplified:             743
% 0.88/1.00  prop_fo_subsumed:                       10
% 0.88/1.00  prop_solver_time:                       0.
% 0.88/1.00  smt_solver_time:                        0.
% 0.88/1.00  smt_fast_solver_time:                   0.
% 0.88/1.00  prop_fast_solver_time:                  0.
% 0.88/1.00  prop_unsat_core_time:                   0.
% 0.88/1.00  
% 0.88/1.00  ------ QBF
% 0.88/1.00  
% 0.88/1.00  qbf_q_res:                              0
% 0.88/1.00  qbf_num_tautologies:                    0
% 0.88/1.00  qbf_prep_cycles:                        0
% 0.88/1.00  
% 0.88/1.00  ------ BMC1
% 0.88/1.00  
% 0.88/1.00  bmc1_current_bound:                     -1
% 0.88/1.00  bmc1_last_solved_bound:                 -1
% 0.88/1.00  bmc1_unsat_core_size:                   -1
% 0.88/1.00  bmc1_unsat_core_parents_size:           -1
% 0.88/1.00  bmc1_merge_next_fun:                    0
% 0.88/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.88/1.00  
% 0.88/1.00  ------ Instantiation
% 0.88/1.00  
% 0.88/1.00  inst_num_of_clauses:                    39
% 0.88/1.00  inst_num_in_passive:                    3
% 0.88/1.00  inst_num_in_active:                     24
% 0.88/1.00  inst_num_in_unprocessed:                12
% 0.88/1.00  inst_num_of_loops:                      30
% 0.88/1.00  inst_num_of_learning_restarts:          0
% 0.88/1.00  inst_num_moves_active_passive:          1
% 0.88/1.00  inst_lit_activity:                      0
% 0.88/1.00  inst_lit_activity_moves:                0
% 0.88/1.00  inst_num_tautologies:                   0
% 0.88/1.00  inst_num_prop_implied:                  0
% 0.88/1.00  inst_num_existing_simplified:           0
% 0.88/1.00  inst_num_eq_res_simplified:             0
% 0.88/1.00  inst_num_child_elim:                    0
% 0.88/1.00  inst_num_of_dismatching_blockings:      4
% 0.88/1.00  inst_num_of_non_proper_insts:           33
% 0.88/1.00  inst_num_of_duplicates:                 0
% 0.88/1.00  inst_inst_num_from_inst_to_res:         0
% 0.88/1.00  inst_dismatching_checking_time:         0.
% 0.88/1.00  
% 0.88/1.00  ------ Resolution
% 0.88/1.00  
% 0.88/1.00  res_num_of_clauses:                     0
% 0.88/1.00  res_num_in_passive:                     0
% 0.88/1.00  res_num_in_active:                      0
% 0.88/1.00  res_num_of_loops:                       35
% 0.88/1.00  res_forward_subset_subsumed:            8
% 0.88/1.00  res_backward_subset_subsumed:           1
% 0.88/1.00  res_forward_subsumed:                   0
% 0.88/1.00  res_backward_subsumed:                  0
% 0.88/1.00  res_forward_subsumption_resolution:     0
% 0.88/1.00  res_backward_subsumption_resolution:    0
% 0.88/1.00  res_clause_to_clause_subsumption:       6
% 0.88/1.00  res_orphan_elimination:                 0
% 0.88/1.00  res_tautology_del:                      8
% 0.88/1.00  res_num_eq_res_simplified:              0
% 0.88/1.00  res_num_sel_changes:                    0
% 0.88/1.00  res_moves_from_active_to_pass:          0
% 0.88/1.00  
% 0.88/1.00  ------ Superposition
% 0.88/1.00  
% 0.88/1.00  sup_time_total:                         0.
% 0.88/1.00  sup_time_generating:                    0.
% 0.88/1.00  sup_time_sim_full:                      0.
% 0.88/1.00  sup_time_sim_immed:                     0.
% 0.88/1.00  
% 0.88/1.00  sup_num_of_clauses:                     6
% 0.88/1.00  sup_num_in_active:                      6
% 0.88/1.00  sup_num_in_passive:                     0
% 0.88/1.00  sup_num_of_loops:                       5
% 0.88/1.00  sup_fw_superposition:                   1
% 0.88/1.00  sup_bw_superposition:                   2
% 0.88/1.00  sup_immediate_simplified:               0
% 0.88/1.00  sup_given_eliminated:                   0
% 0.88/1.00  comparisons_done:                       0
% 0.88/1.00  comparisons_avoided:                    0
% 0.88/1.00  
% 0.88/1.00  ------ Simplifications
% 0.88/1.00  
% 0.88/1.00  
% 0.88/1.00  sim_fw_subset_subsumed:                 0
% 0.88/1.00  sim_bw_subset_subsumed:                 0
% 0.88/1.00  sim_fw_subsumed:                        0
% 0.88/1.00  sim_bw_subsumed:                        0
% 0.88/1.00  sim_fw_subsumption_res:                 0
% 0.88/1.00  sim_bw_subsumption_res:                 0
% 0.88/1.00  sim_tautology_del:                      0
% 0.88/1.00  sim_eq_tautology_del:                   0
% 0.88/1.00  sim_eq_res_simp:                        0
% 0.88/1.00  sim_fw_demodulated:                     0
% 0.88/1.00  sim_bw_demodulated:                     0
% 0.88/1.00  sim_light_normalised:                   0
% 0.88/1.00  sim_joinable_taut:                      0
% 0.88/1.00  sim_joinable_simp:                      0
% 0.88/1.00  sim_ac_normalised:                      0
% 0.88/1.00  sim_smt_subsumption:                    0
% 0.88/1.00  
%------------------------------------------------------------------------------
