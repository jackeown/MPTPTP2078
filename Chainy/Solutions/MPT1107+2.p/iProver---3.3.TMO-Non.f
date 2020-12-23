%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1107+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Timeout 59.45s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   69 ( 147 expanded)
%              Number of clauses        :   34 (  43 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  189 ( 402 expanded)
%              Number of equality atoms :   67 ( 132 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1792,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1793,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f1792])).

fof(f3810,plain,(
    ? [X0] :
      ( ? [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1793])).

fof(f5396,plain,(
    ! [X0] :
      ( ? [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_struct_0(k1_pre_topc(X0,sK666)) != sK666
        & m1_subset_1(sK666,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f5395,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( u1_struct_0(k1_pre_topc(X0,X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( u1_struct_0(k1_pre_topc(sK665,X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK665))) )
      & l1_pre_topc(sK665) ) ),
    introduced(choice_axiom,[])).

fof(f5397,plain,
    ( u1_struct_0(k1_pre_topc(sK665,sK666)) != sK666
    & m1_subset_1(sK666,k1_zfmisc_1(u1_struct_0(sK665)))
    & l1_pre_topc(sK665) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK665,sK666])],[f3810,f5396,f5395])).

fof(f8904,plain,(
    m1_subset_1(sK666,k1_zfmisc_1(u1_struct_0(sK665))) ),
    inference(cnf_transformation,[],[f5397])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8346,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f10661,plain,(
    m1_subset_1(sK666,k9_setfam_1(u1_struct_0(sK665))) ),
    inference(definition_unfolding,[],[f8904,f8346])).

fof(f1767,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3784,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1767])).

fof(f3785,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3784])).

fof(f8873,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3785])).

fof(f10646,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f8873,f8346])).

fof(f8903,plain,(
    l1_pre_topc(sK665) ),
    inference(cnf_transformation,[],[f5397])).

fof(f1772,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3789,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1772])).

fof(f8877,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3789])).

fof(f1770,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3788,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1770])).

fof(f8876,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3788])).

fof(f1764,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3781,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1764])).

fof(f8856,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3781])).

fof(f1761,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3776,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1761])).

fof(f3777,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3776])).

fof(f5364,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3777])).

fof(f8841,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f5364])).

fof(f10630,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f8841,f8346])).

fof(f11061,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f10630])).

fof(f8872,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3785])).

fof(f10647,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f8872,f8346])).

fof(f8905,plain,(
    u1_struct_0(k1_pre_topc(sK665,sK666)) != sK666 ),
    inference(cnf_transformation,[],[f5397])).

cnf(c_3479,negated_conjecture,
    ( m1_subset_1(sK666,k9_setfam_1(u1_struct_0(sK665))) ),
    inference(cnf_transformation,[],[f10661])).

cnf(c_101369,plain,
    ( m1_subset_1(sK666,k9_setfam_1(u1_struct_0(sK665))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3479])).

cnf(c_3447,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f10646])).

cnf(c_101398,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3447])).

cnf(c_158622,plain,
    ( m1_pre_topc(k1_pre_topc(sK665,sK666),sK665) = iProver_top
    | l1_pre_topc(sK665) != iProver_top ),
    inference(superposition,[status(thm)],[c_101369,c_101398])).

cnf(c_3480,negated_conjecture,
    ( l1_pre_topc(sK665) ),
    inference(cnf_transformation,[],[f8903])).

cnf(c_3482,plain,
    ( l1_pre_topc(sK665) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3480])).

cnf(c_3483,plain,
    ( m1_subset_1(sK666,k9_setfam_1(u1_struct_0(sK665))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3479])).

cnf(c_136181,plain,
    ( m1_pre_topc(k1_pre_topc(sK665,X0),sK665)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK665)))
    | ~ l1_pre_topc(sK665) ),
    inference(instantiation,[status(thm)],[c_3447])).

cnf(c_154711,plain,
    ( m1_pre_topc(k1_pre_topc(sK665,sK666),sK665)
    | ~ m1_subset_1(sK666,k9_setfam_1(u1_struct_0(sK665)))
    | ~ l1_pre_topc(sK665) ),
    inference(instantiation,[status(thm)],[c_136181])).

cnf(c_154712,plain,
    ( m1_pre_topc(k1_pre_topc(sK665,sK666),sK665) = iProver_top
    | m1_subset_1(sK666,k9_setfam_1(u1_struct_0(sK665))) != iProver_top
    | l1_pre_topc(sK665) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154711])).

cnf(c_159450,plain,
    ( m1_pre_topc(k1_pre_topc(sK665,sK666),sK665) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_158622,c_3482,c_3483,c_154712])).

cnf(c_3452,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f8877])).

cnf(c_101393,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3452])).

cnf(c_159455,plain,
    ( l1_pre_topc(k1_pre_topc(sK665,sK666)) = iProver_top
    | l1_pre_topc(sK665) != iProver_top ),
    inference(superposition,[status(thm)],[c_159450,c_101393])).

cnf(c_160735,plain,
    ( l1_pre_topc(k1_pre_topc(sK665,sK666)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_159455,c_3482])).

cnf(c_3451,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f8876])).

cnf(c_101394,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3451])).

cnf(c_160740,plain,
    ( l1_struct_0(k1_pre_topc(sK665,sK666)) = iProver_top ),
    inference(superposition,[status(thm)],[c_160735,c_101394])).

cnf(c_3431,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f8856])).

cnf(c_101414,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3431])).

cnf(c_200575,plain,
    ( k2_struct_0(k1_pre_topc(sK665,sK666)) = u1_struct_0(k1_pre_topc(sK665,sK666)) ),
    inference(superposition,[status(thm)],[c_160740,c_101414])).

cnf(c_3417,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f11061])).

cnf(c_30936,plain,
    ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3417,c_3447])).

cnf(c_30937,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_30936])).

cnf(c_3448,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f10647])).

cnf(c_30942,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30937,c_3448])).

cnf(c_30943,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_30942])).

cnf(c_101287,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30943])).

cnf(c_132720,plain,
    ( k2_struct_0(k1_pre_topc(sK665,sK666)) = sK666
    | l1_pre_topc(sK665) != iProver_top ),
    inference(superposition,[status(thm)],[c_101369,c_101287])).

cnf(c_132751,plain,
    ( k2_struct_0(k1_pre_topc(sK665,sK666)) = sK666 ),
    inference(global_propositional_subsumption,[status(thm)],[c_132720,c_3482])).

cnf(c_200589,plain,
    ( u1_struct_0(k1_pre_topc(sK665,sK666)) = sK666 ),
    inference(light_normalisation,[status(thm)],[c_200575,c_132751])).

cnf(c_3478,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(sK665,sK666)) != sK666 ),
    inference(cnf_transformation,[],[f8905])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_200589,c_3478])).

%------------------------------------------------------------------------------
