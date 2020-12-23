%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1851+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:40 EST 2020

% Result     : Theorem 0.35s
% Output     : CNFRefutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 139 expanded)
%              Number of clauses        :   35 (  43 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  162 ( 561 expanded)
%              Number of equality atoms :   82 ( 173 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v2_tdlat_3(sK1)
        & v2_tdlat_3(X0)
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tdlat_3(X1)
            & v2_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ v2_tdlat_3(sK1)
    & v2_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13,f12])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_175,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_176,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_186,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X1))
    | u1_pre_topc(sK0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_176])).

cnf(c_187,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,u1_pre_topc(sK0))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_424,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(equality_resolution,[status(thm)],[c_187])).

cnf(c_7,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_425,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_424,c_7])).

cnf(c_430,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_425])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_tdlat_3(X0)
    | k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_6,negated_conjecture,
    ( v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_153,plain,
    ( ~ l1_pre_topc(X0)
    | k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_154,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tarski(k1_xboole_0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_153])).

cnf(c_22,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | k2_tarski(k1_xboole_0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_156,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_154,c_9,c_6,c_22])).

cnf(c_514,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_430,c_156])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_198,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X1) != g1_pre_topc(X3,X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X2))
    | u1_pre_topc(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_176])).

cnf(c_199,plain,
    ( X0 = u1_pre_topc(sK0)
    | g1_pre_topc(X1,u1_pre_topc(sK0)) != g1_pre_topc(X2,X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_315,plain,
    ( X0 = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X1,X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_388,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_254,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_326,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != X0
    | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_356,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != u1_pre_topc(X0)
    | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_358,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != u1_pre_topc(sK0)
    | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_253,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_314,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | v2_tdlat_3(X0)
    | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_145,plain,
    ( ~ l1_pre_topc(X0)
    | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_146,plain,
    ( ~ l1_pre_topc(sK1)
    | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_8,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_514,c_388,c_358,c_314,c_146,c_7,c_8])).


%------------------------------------------------------------------------------
