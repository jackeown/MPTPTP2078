%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1278+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Timeout 59.28s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   81 ( 182 expanded)
%              Number of clauses        :   30 (  36 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  304 ( 771 expanded)
%              Number of equality atoms :  133 ( 264 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5065,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f5066,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f5065])).

fof(f6931,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5066])).

fof(f13321,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f6931])).

fof(f2187,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2188,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2187])).

fof(f4907,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2188])).

fof(f4908,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f4907])).

fof(f6862,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK790
        & v3_tops_1(sK790,X0)
        & v3_pre_topc(sK790,X0)
        & m1_subset_1(sK790,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f6861,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK789)
          & v3_pre_topc(X1,sK789)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK789))) )
      & l1_pre_topc(sK789)
      & v2_pre_topc(sK789) ) ),
    introduced(choice_axiom,[])).

fof(f6863,plain,
    ( k1_xboole_0 != sK790
    & v3_tops_1(sK790,sK789)
    & v3_pre_topc(sK790,sK789)
    & m1_subset_1(sK790,k1_zfmisc_1(u1_struct_0(sK789)))
    & l1_pre_topc(sK789)
    & v2_pre_topc(sK789) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK789,sK790])],[f4908,f6862,f6861])).

fof(f11154,plain,(
    m1_subset_1(sK790,k1_zfmisc_1(u1_struct_0(sK789))) ),
    inference(cnf_transformation,[],[f6863])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9812,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f13310,plain,(
    m1_subset_1(sK790,k9_setfam_1(u1_struct_0(sK789))) ),
    inference(definition_unfolding,[],[f11154,f9812])).

fof(f2177,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4888,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2177])).

fof(f4889,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f4888])).

fof(f6849,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k1_xboole_0 = X2
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f4889])).

fof(f6850,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f6849])).

fof(f6851,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK786(X0,X1)
        & v3_pre_topc(sK786(X0,X1),X0)
        & r1_tarski(sK786(X0,X1),X1)
        & m1_subset_1(sK786(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f6852,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ( k1_xboole_0 != sK786(X0,X1)
                & v3_pre_topc(sK786(X0,X1),X0)
                & r1_tarski(sK786(X0,X1),X1)
                & m1_subset_1(sK786(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK786])],[f6850,f6851])).

fof(f11125,plain,(
    ! [X0,X3,X1] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f6852])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6871,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f13289,plain,(
    ! [X0,X3,X1] :
      ( o_0_0_xboole_0 = X3
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f11125,f6871,f9812,f9812])).

fof(f11152,plain,(
    v2_pre_topc(sK789) ),
    inference(cnf_transformation,[],[f6863])).

fof(f11153,plain,(
    l1_pre_topc(sK789) ),
    inference(cnf_transformation,[],[f6863])).

fof(f11155,plain,(
    v3_pre_topc(sK790,sK789) ),
    inference(cnf_transformation,[],[f6863])).

fof(f11157,plain,(
    k1_xboole_0 != sK790 ),
    inference(cnf_transformation,[],[f6863])).

fof(f13309,plain,(
    o_0_0_xboole_0 != sK790 ),
    inference(definition_unfolding,[],[f11157,f6871])).

fof(f1371,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6033,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1371])).

fof(f6034,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f6033])).

fof(f9267,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6034])).

fof(f1283,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9075,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1283])).

fof(f1281,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9073,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1281])).

fof(f11168,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f9075,f9073])).

fof(f12249,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f9267,f6871,f11168,f6871,f6871,f6871,f6871])).

fof(f9268,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f6034])).

fof(f12248,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f9268,f6871,f6871,f11168])).

fof(f13597,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f12248])).

fof(f11156,plain,(
    v3_tops_1(sK790,sK789) ),
    inference(cnf_transformation,[],[f6863])).

fof(f2182,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4897,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2182])).

fof(f4898,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4897])).

fof(f11146,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4898])).

fof(f13303,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f11146,f9812])).

cnf(c_68,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13321])).

cnf(c_127457,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_4263,negated_conjecture,
    ( m1_subset_1(sK790,k9_setfam_1(u1_struct_0(sK789))) ),
    inference(cnf_transformation,[],[f13310])).

cnf(c_124059,plain,
    ( m1_subset_1(sK790,k9_setfam_1(u1_struct_0(sK789))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4263])).

cnf(c_4237,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f13289])).

cnf(c_124083,plain,
    ( o_0_0_xboole_0 = X0
    | v2_tops_1(X1,X2) != iProver_top
    | v3_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4237])).

cnf(c_172174,plain,
    ( sK790 = o_0_0_xboole_0
    | v2_tops_1(X0,sK789) != iProver_top
    | v3_pre_topc(sK790,sK789) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK789))) != iProver_top
    | r1_tarski(sK790,X0) != iProver_top
    | v2_pre_topc(sK789) != iProver_top
    | l1_pre_topc(sK789) != iProver_top ),
    inference(superposition,[status(thm)],[c_124059,c_124083])).

cnf(c_4265,negated_conjecture,
    ( v2_pre_topc(sK789) ),
    inference(cnf_transformation,[],[f11152])).

cnf(c_4266,plain,
    ( v2_pre_topc(sK789) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4265])).

cnf(c_4264,negated_conjecture,
    ( l1_pre_topc(sK789) ),
    inference(cnf_transformation,[],[f11153])).

cnf(c_4267,plain,
    ( l1_pre_topc(sK789) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4264])).

cnf(c_4262,negated_conjecture,
    ( v3_pre_topc(sK790,sK789) ),
    inference(cnf_transformation,[],[f11155])).

cnf(c_4269,plain,
    ( v3_pre_topc(sK790,sK789) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4262])).

cnf(c_4260,negated_conjecture,
    ( o_0_0_xboole_0 != sK790 ),
    inference(cnf_transformation,[],[f13309])).

cnf(c_2384,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f12249])).

cnf(c_9370,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2383,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0),X1),X2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f13597])).

cnf(c_9371,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2383])).

cnf(c_61926,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_169792,plain,
    ( sK790 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK790 ),
    inference(instantiation,[status(thm)],[c_61926])).

cnf(c_169793,plain,
    ( sK790 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK790
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_169792])).

cnf(c_172948,plain,
    ( v2_tops_1(X0,sK789) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK789))) != iProver_top
    | r1_tarski(sK790,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_172174,c_4266,c_4267,c_4269,c_4260,c_9370,c_9371,c_169793])).

cnf(c_172955,plain,
    ( v2_tops_1(sK790,sK789) != iProver_top
    | r1_tarski(sK790,sK790) != iProver_top ),
    inference(superposition,[status(thm)],[c_124059,c_172948])).

cnf(c_4261,negated_conjecture,
    ( v3_tops_1(sK790,sK789) ),
    inference(cnf_transformation,[],[f11156])).

cnf(c_4270,plain,
    ( v3_tops_1(sK790,sK789) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4261])).

cnf(c_4254,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f13303])).

cnf(c_124066,plain,
    ( v3_tops_1(X0,X1) != iProver_top
    | v2_tops_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4254])).

cnf(c_165251,plain,
    ( v3_tops_1(sK790,sK789) != iProver_top
    | v2_tops_1(sK790,sK789) = iProver_top
    | l1_pre_topc(sK789) != iProver_top ),
    inference(superposition,[status(thm)],[c_124059,c_124066])).

cnf(c_172976,plain,
    ( r1_tarski(sK790,sK790) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_172955,c_4267,c_4270,c_165251])).

cnf(c_176589,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_127457,c_172976])).

%------------------------------------------------------------------------------
