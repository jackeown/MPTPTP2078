%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1290+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:21 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 ( 107 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => r1_tarski(X1,k9_setfam_1(k2_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => r1_tarski(X1,k9_setfam_1(k2_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(X0)))
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(sK0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11,f10])).

fof(f18,plain,(
    ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,plain,(
    ~ r1_tarski(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f18,f14])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_2,negated_conjecture,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_66,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_zfmisc_1(k2_struct_0(sK0)) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_67,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_66])).

cnf(c_112,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_67])).

cnf(c_166,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_112])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_114,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_165,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_114])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_4,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_60,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_61,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_60])).

cnf(c_113,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_61])).

cnf(c_169,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_165,c_113])).

cnf(c_173,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_166,c_169])).


%------------------------------------------------------------------------------
