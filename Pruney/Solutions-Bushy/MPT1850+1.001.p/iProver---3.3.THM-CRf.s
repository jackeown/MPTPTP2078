%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1850+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:40 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 244 expanded)
%              Number of clauses        :   37 (  63 expanded)
%              Number of leaves         :    9 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  177 ( 959 expanded)
%              Number of equality atoms :   93 ( 289 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v1_tdlat_3(sK1)
        & v1_tdlat_3(X0)
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tdlat_3(X1)
            & v1_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ v1_tdlat_3(sK1)
    & v1_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14,f13])).

fof(f24,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k1_zfmisc_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f16,f21])).

fof(f25,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f26,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_7,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_174,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_175,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_185,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X1))
    | u1_pre_topc(sK0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_175])).

cnf(c_186,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,u1_pre_topc(sK0))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_tdlat_3(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6,negated_conjecture,
    ( v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_152,plain,
    ( ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) = u1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_153,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_22,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_155,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_153,c_9,c_6,c_22])).

cnf(c_276,plain,
    ( X0 = X1
    | g1_pre_topc(X0,u1_pre_topc(sK0)) != g1_pre_topc(X1,X2)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(u1_pre_topc(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_186,c_155])).

cnf(c_431,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(u1_pre_topc(sK0))
    | u1_struct_0(sK0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_276])).

cnf(c_443,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | k1_zfmisc_1(u1_pre_topc(sK0)) != k1_zfmisc_1(u1_pre_topc(sK0))
    | u1_struct_0(sK0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_431,c_155])).

cnf(c_444,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_443])).

cnf(c_619,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_444])).

cnf(c_858,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_619,c_155])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_197,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X1) != g1_pre_topc(X3,X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X2))
    | u1_pre_topc(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_175])).

cnf(c_198,plain,
    ( X0 = u1_pre_topc(sK0)
    | g1_pre_topc(X1,u1_pre_topc(sK0)) != g1_pre_topc(X2,X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_314,plain,
    ( X0 = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X1,X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_387,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_252,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_325,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_355,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != u1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_357,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != u1_pre_topc(sK0)
    | k1_zfmisc_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_251,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_313,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | v1_tdlat_3(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,negated_conjecture,
    ( ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_144,plain,
    ( ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != u1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_145,plain,
    ( ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_8,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_858,c_387,c_357,c_313,c_145,c_7,c_8])).


%------------------------------------------------------------------------------
