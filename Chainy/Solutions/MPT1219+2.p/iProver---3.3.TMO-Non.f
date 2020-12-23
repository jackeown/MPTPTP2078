%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1219+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Timeout 58.93s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   52 ( 102 expanded)
%              Number of clauses        :   25 (  27 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 338 expanded)
%              Number of equality atoms :   67 ( 147 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5076,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f7495,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5076])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9474,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f11253,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f7495,f9474])).

fof(f2086,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2087,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f2086])).

fof(f4631,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2087])).

fof(f4632,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f4631])).

fof(f6524,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK770 != X1
        & k3_subset_1(u1_struct_0(X0),sK770) = k3_subset_1(u1_struct_0(X0),X1)
        & m1_subset_1(sK770,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f6523,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( sK769 != X2
            & k3_subset_1(u1_struct_0(X0),sK769) = k3_subset_1(u1_struct_0(X0),X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK769,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f6522,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(sK768),X1) = k3_subset_1(u1_struct_0(sK768),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK768))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK768))) )
      & l1_struct_0(sK768) ) ),
    introduced(choice_axiom,[])).

fof(f6525,plain,
    ( sK769 != sK770
    & k3_subset_1(u1_struct_0(sK768),sK769) = k3_subset_1(u1_struct_0(sK768),sK770)
    & m1_subset_1(sK770,k1_zfmisc_1(u1_struct_0(sK768)))
    & m1_subset_1(sK769,k1_zfmisc_1(u1_struct_0(sK768)))
    & l1_struct_0(sK768) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK768,sK769,sK770])],[f4632,f6524,f6523,f6522])).

fof(f10648,plain,(
    m1_subset_1(sK769,k1_zfmisc_1(u1_struct_0(sK768))) ),
    inference(cnf_transformation,[],[f6525])).

fof(f12666,plain,(
    m1_subset_1(sK769,k9_setfam_1(u1_struct_0(sK768))) ),
    inference(definition_unfolding,[],[f10648,f9474])).

fof(f10649,plain,(
    m1_subset_1(sK770,k1_zfmisc_1(u1_struct_0(sK768))) ),
    inference(cnf_transformation,[],[f6525])).

fof(f12665,plain,(
    m1_subset_1(sK770,k9_setfam_1(u1_struct_0(sK768))) ),
    inference(definition_unfolding,[],[f10649,f9474])).

fof(f10650,plain,(
    k3_subset_1(u1_struct_0(sK768),sK769) = k3_subset_1(u1_struct_0(sK768),sK770) ),
    inference(cnf_transformation,[],[f6525])).

fof(f536,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2464,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f536])).

fof(f2465,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2464])).

fof(f7375,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2465])).

fof(f11190,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f7375,f9474,f9474])).

fof(f7496,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5076])).

fof(f11252,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f7496,f9474])).

fof(f10651,plain,(
    sK769 != sK770 ),
    inference(cnf_transformation,[],[f6525])).

cnf(c_59342,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_183339,plain,
    ( sK769 = sK769 ),
    inference(instantiation,[status(thm)],[c_59342])).

cnf(c_59343,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_164148,plain,
    ( sK770 != X0
    | sK769 != X0
    | sK769 = sK770 ),
    inference(instantiation,[status(thm)],[c_59343])).

cnf(c_183338,plain,
    ( sK770 != sK769
    | sK769 = sK770
    | sK769 != sK769 ),
    inference(instantiation,[status(thm)],[c_164148])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11253])).

cnf(c_4096,negated_conjecture,
    ( m1_subset_1(sK769,k9_setfam_1(u1_struct_0(sK768))) ),
    inference(cnf_transformation,[],[f12666])).

cnf(c_160795,plain,
    ( r1_tarski(sK769,u1_struct_0(sK768)) ),
    inference(resolution,[status(thm)],[c_956,c_4096])).

cnf(c_4095,negated_conjecture,
    ( m1_subset_1(sK770,k9_setfam_1(u1_struct_0(sK768))) ),
    inference(cnf_transformation,[],[f12665])).

cnf(c_160793,plain,
    ( r1_tarski(sK770,u1_struct_0(sK768)) ),
    inference(resolution,[status(thm)],[c_956,c_4095])).

cnf(c_4094,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK768),sK769) = k3_subset_1(u1_struct_0(sK768),sK770) ),
    inference(cnf_transformation,[],[f10650])).

cnf(c_835,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k9_setfam_1(X1))
    | X0 = X2
    | k3_subset_1(X1,X0) != k3_subset_1(X1,X2) ),
    inference(cnf_transformation,[],[f11190])).

cnf(c_955,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11252])).

cnf(c_25856,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k9_setfam_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_955])).

cnf(c_25857,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_25856])).

cnf(c_31043,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r1_tarski(X2,X1)
    | X2 = X0
    | k3_subset_1(X1,X2) != k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_835,c_25857])).

cnf(c_46792,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k9_setfam_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_955])).

cnf(c_46793,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_46792])).

cnf(c_51808,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | X2 = X0
    | k3_subset_1(X1,X2) != k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_31043,c_46793])).

cnf(c_118677,plain,
    ( X0 = X1
    | k3_subset_1(X2,X0) != k3_subset_1(X2,X1)
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51808])).

cnf(c_157162,plain,
    ( k3_subset_1(u1_struct_0(sK768),X0) != k3_subset_1(u1_struct_0(sK768),sK769)
    | sK770 = X0
    | r1_tarski(X0,u1_struct_0(sK768)) != iProver_top
    | r1_tarski(sK770,u1_struct_0(sK768)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4094,c_118677])).

cnf(c_157210,plain,
    ( sK770 = sK769
    | r1_tarski(sK770,u1_struct_0(sK768)) != iProver_top
    | r1_tarski(sK769,u1_struct_0(sK768)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_157162])).

cnf(c_157217,plain,
    ( ~ r1_tarski(sK770,u1_struct_0(sK768))
    | ~ r1_tarski(sK769,u1_struct_0(sK768))
    | sK770 = sK769 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_157210])).

cnf(c_4093,negated_conjecture,
    ( sK769 != sK770 ),
    inference(cnf_transformation,[],[f10651])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_183339,c_183338,c_160795,c_160793,c_157217,c_4093])).

%------------------------------------------------------------------------------
