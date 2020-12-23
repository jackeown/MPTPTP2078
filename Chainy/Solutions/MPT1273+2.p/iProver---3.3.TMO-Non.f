%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1273+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Timeout 59.10s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   39 (  64 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 221 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2175,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2176,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v2_tops_1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f2175])).

fof(f4871,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2176])).

fof(f4872,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4871])).

fof(f6823,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tops_1(sK789,X0)
        & v3_tops_1(sK789,X0)
        & m1_subset_1(sK789,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f6822,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tops_1(X1,X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tops_1(X1,sK788)
          & v3_tops_1(X1,sK788)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK788))) )
      & l1_pre_topc(sK788) ) ),
    introduced(choice_axiom,[])).

fof(f6824,plain,
    ( ~ v2_tops_1(sK789,sK788)
    & v3_tops_1(sK789,sK788)
    & m1_subset_1(sK789,k1_zfmisc_1(u1_struct_0(sK788)))
    & l1_pre_topc(sK788) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK788,sK789])],[f4872,f6823,f6822])).

fof(f11099,plain,(
    m1_subset_1(sK789,k1_zfmisc_1(u1_struct_0(sK788))) ),
    inference(cnf_transformation,[],[f6824])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9773,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f13240,plain,(
    m1_subset_1(sK789,k9_setfam_1(u1_struct_0(sK788))) ),
    inference(definition_unfolding,[],[f11099,f9773])).

fof(f2174,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4869,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2174])).

fof(f4870,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4869])).

fof(f11097,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4870])).

fof(f13239,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f11097,f9773])).

fof(f2092,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4729,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2092])).

fof(f6769,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f4729])).

fof(f10954,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f6769])).

fof(f13122,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f10954,f9773])).

fof(f11101,plain,(
    ~ v2_tops_1(sK789,sK788) ),
    inference(cnf_transformation,[],[f6824])).

fof(f11100,plain,(
    v3_tops_1(sK789,sK788) ),
    inference(cnf_transformation,[],[f6824])).

fof(f11098,plain,(
    l1_pre_topc(sK788) ),
    inference(cnf_transformation,[],[f6824])).

cnf(c_4247,negated_conjecture,
    ( m1_subset_1(sK789,k9_setfam_1(u1_struct_0(sK788))) ),
    inference(cnf_transformation,[],[f13240])).

cnf(c_123667,plain,
    ( m1_subset_1(sK789,k9_setfam_1(u1_struct_0(sK788))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4247])).

cnf(c_4244,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f13239])).

cnf(c_123670,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) = iProver_top
    | v3_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4244])).

cnf(c_4100,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f13122])).

cnf(c_123815,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) != iProver_top
    | v2_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4100])).

cnf(c_170994,plain,
    ( v3_tops_1(X0,X1) != iProver_top
    | v2_tops_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_123670,c_123815])).

cnf(c_176900,plain,
    ( v3_tops_1(sK789,sK788) != iProver_top
    | v2_tops_1(sK789,sK788) = iProver_top
    | l1_pre_topc(sK788) != iProver_top ),
    inference(superposition,[status(thm)],[c_123667,c_170994])).

cnf(c_4245,negated_conjecture,
    ( ~ v2_tops_1(sK789,sK788) ),
    inference(cnf_transformation,[],[f11101])).

cnf(c_4252,plain,
    ( v2_tops_1(sK789,sK788) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4245])).

cnf(c_4246,negated_conjecture,
    ( v3_tops_1(sK789,sK788) ),
    inference(cnf_transformation,[],[f11100])).

cnf(c_4251,plain,
    ( v3_tops_1(sK789,sK788) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4246])).

cnf(c_4248,negated_conjecture,
    ( l1_pre_topc(sK788) ),
    inference(cnf_transformation,[],[f11098])).

cnf(c_4249,plain,
    ( l1_pre_topc(sK788) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4248])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_176900,c_4252,c_4251,c_4249])).

%------------------------------------------------------------------------------
