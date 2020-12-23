%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:51 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 119 expanded)
%              Number of clauses        :   41 (  54 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :  170 ( 271 expanded)
%              Number of equality atoms :   39 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_75,plain,
    ( r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_2,c_0])).

cnf(c_76,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_75])).

cnf(c_230,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k7_relat_1(X0_39,X0_40),k7_relat_1(X1_39,X0_40))
    | ~ v1_relat_1(X1_39) ),
    inference(subtyping,[status(esa)],[c_76])).

cnf(c_1919,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(k7_relat_1(X0_39,X0_40),k7_relat_1(X1_39,X0_40)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_233,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1921,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_237,plain,
    ( ~ v1_relat_1(X0_39)
    | v1_relat_1(k7_relat_1(X0_39,X0_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1915,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k7_relat_1(X0_39,X0_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_236,plain,
    ( ~ v1_relat_1(X0_39)
    | k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1916,plain,
    ( k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_2013,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0_39,X0_40),X1_40)) = k9_relat_1(k7_relat_1(X0_39,X0_40),X1_40)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_1916])).

cnf(c_2069,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_40),X1_40)) = k9_relat_1(k7_relat_1(sK2,X0_40),X1_40) ),
    inference(superposition,[status(thm)],[c_1921,c_2013])).

cnf(c_2012,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_40)) = k9_relat_1(sK2,X0_40) ),
    inference(superposition,[status(thm)],[c_1921,c_1916])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_69,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_2,c_0])).

cnf(c_70,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_69])).

cnf(c_231,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k2_relat_1(X0_39),k2_relat_1(X1_39))
    | ~ v1_relat_1(X1_39) ),
    inference(subtyping,[status(esa)],[c_70])).

cnf(c_1918,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(k2_relat_1(X0_39),k2_relat_1(X1_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_2212,plain,
    ( r1_tarski(X0_39,k7_relat_1(sK2,X0_40)) != iProver_top
    | r1_tarski(k2_relat_1(X0_39),k9_relat_1(sK2,X0_40)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_1918])).

cnf(c_11,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1983,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_40))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_1984,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_40)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_2381,plain,
    ( r1_tarski(k2_relat_1(X0_39),k9_relat_1(sK2,X0_40)) = iProver_top
    | r1_tarski(X0_39,k7_relat_1(sK2,X0_40)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2212,c_11,c_1984])).

cnf(c_2382,plain,
    ( r1_tarski(X0_39,k7_relat_1(sK2,X0_40)) != iProver_top
    | r1_tarski(k2_relat_1(X0_39),k9_relat_1(sK2,X0_40)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2381])).

cnf(c_2390,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_40),X1_40),k9_relat_1(sK2,X2_40)) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK2,X0_40),X1_40),k7_relat_1(sK2,X2_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2069,c_2382])).

cnf(c_2531,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_40),X1_40),k9_relat_1(sK2,X1_40)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0_40),sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1919,c_2390])).

cnf(c_8,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_235,plain,
    ( r1_tarski(k7_relat_1(X0_39,X0_40),X0_39)
    | ~ v1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1982,plain,
    ( r1_tarski(k7_relat_1(sK2,X0_40),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_1986,plain,
    ( r1_tarski(k7_relat_1(sK2,X0_40),sK2) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1982])).

cnf(c_10136,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_40),X1_40),k9_relat_1(sK2,X1_40)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2531,c_11,c_1986])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_234,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1922,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_10141,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_10136,c_1922])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.81/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/1.00  
% 3.81/1.00  ------  iProver source info
% 3.81/1.00  
% 3.81/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.81/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/1.00  git: non_committed_changes: false
% 3.81/1.00  git: last_make_outside_of_git: false
% 3.81/1.00  
% 3.81/1.00  ------ 
% 3.81/1.00  ------ Parsing...
% 3.81/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  ------ Proving...
% 3.81/1.00  ------ Problem Properties 
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  clauses                                 9
% 3.81/1.00  conjectures                             2
% 3.81/1.00  EPR                                     2
% 3.81/1.00  Horn                                    9
% 3.81/1.00  unary                                   2
% 3.81/1.00  binary                                  3
% 3.81/1.00  lits                                    20
% 3.81/1.00  lits eq                                 1
% 3.81/1.00  fd_pure                                 0
% 3.81/1.00  fd_pseudo                               0
% 3.81/1.00  fd_cond                                 0
% 3.81/1.00  fd_pseudo_cond                          0
% 3.81/1.00  AC symbols                              0
% 3.81/1.00  
% 3.81/1.00  ------ Input Options Time Limit: Unbounded
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing...
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.81/1.00  Current options:
% 3.81/1.00  ------ 
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing...
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  % SZS status Theorem for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00   Resolution empty clause
% 3.81/1.00  
% 3.81/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  fof(f4,axiom,(
% 3.81/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f12,plain,(
% 3.81/1.00    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.81/1.00    inference(ennf_transformation,[],[f4])).
% 3.81/1.00  
% 3.81/1.00  fof(f13,plain,(
% 3.81/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.81/1.00    inference(flattening,[],[f12])).
% 3.81/1.00  
% 3.81/1.00  fof(f26,plain,(
% 3.81/1.00    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f13])).
% 3.81/1.00  
% 3.81/1.00  fof(f2,axiom,(
% 3.81/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f10,plain,(
% 3.81/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.81/1.00    inference(ennf_transformation,[],[f2])).
% 3.81/1.00  
% 3.81/1.00  fof(f24,plain,(
% 3.81/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f10])).
% 3.81/1.00  
% 3.81/1.00  fof(f1,axiom,(
% 3.81/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f19,plain,(
% 3.81/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.81/1.00    inference(nnf_transformation,[],[f1])).
% 3.81/1.00  
% 3.81/1.00  fof(f23,plain,(
% 3.81/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f19])).
% 3.81/1.00  
% 3.81/1.00  fof(f8,conjecture,(
% 3.81/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f9,negated_conjecture,(
% 3.81/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 3.81/1.00    inference(negated_conjecture,[],[f8])).
% 3.81/1.00  
% 3.81/1.00  fof(f18,plain,(
% 3.81/1.00    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 3.81/1.00    inference(ennf_transformation,[],[f9])).
% 3.81/1.00  
% 3.81/1.00  fof(f20,plain,(
% 3.81/1.00    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 3.81/1.00    introduced(choice_axiom,[])).
% 3.81/1.00  
% 3.81/1.00  fof(f21,plain,(
% 3.81/1.00    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 3.81/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).
% 3.81/1.00  
% 3.81/1.00  fof(f31,plain,(
% 3.81/1.00    v1_relat_1(sK2)),
% 3.81/1.00    inference(cnf_transformation,[],[f21])).
% 3.81/1.00  
% 3.81/1.00  fof(f3,axiom,(
% 3.81/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f11,plain,(
% 3.81/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.81/1.00    inference(ennf_transformation,[],[f3])).
% 3.81/1.00  
% 3.81/1.00  fof(f25,plain,(
% 3.81/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f11])).
% 3.81/1.00  
% 3.81/1.00  fof(f5,axiom,(
% 3.81/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f14,plain,(
% 3.81/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.81/1.00    inference(ennf_transformation,[],[f5])).
% 3.81/1.00  
% 3.81/1.00  fof(f27,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f14])).
% 3.81/1.00  
% 3.81/1.00  fof(f6,axiom,(
% 3.81/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f15,plain,(
% 3.81/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.81/1.00    inference(ennf_transformation,[],[f6])).
% 3.81/1.00  
% 3.81/1.00  fof(f16,plain,(
% 3.81/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.81/1.00    inference(flattening,[],[f15])).
% 3.81/1.00  
% 3.81/1.00  fof(f29,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f16])).
% 3.81/1.00  
% 3.81/1.00  fof(f7,axiom,(
% 3.81/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f17,plain,(
% 3.81/1.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.81/1.00    inference(ennf_transformation,[],[f7])).
% 3.81/1.00  
% 3.81/1.00  fof(f30,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f17])).
% 3.81/1.00  
% 3.81/1.00  fof(f32,plain,(
% 3.81/1.00    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))),
% 3.81/1.00    inference(cnf_transformation,[],[f21])).
% 3.81/1.00  
% 3.81/1.00  cnf(c_4,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,X1)
% 3.81/1.00      | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
% 3.81/1.00      | ~ v1_relat_1(X0)
% 3.81/1.00      | ~ v1_relat_1(X1) ),
% 3.81/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2,plain,
% 3.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.81/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_0,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.81/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_75,plain,
% 3.81/1.00      ( r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
% 3.81/1.00      | ~ r1_tarski(X0,X1)
% 3.81/1.00      | ~ v1_relat_1(X1) ),
% 3.81/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4,c_2,c_0]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_76,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,X1)
% 3.81/1.00      | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
% 3.81/1.00      | ~ v1_relat_1(X1) ),
% 3.81/1.00      inference(renaming,[status(thm)],[c_75]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_230,plain,
% 3.81/1.00      ( ~ r1_tarski(X0_39,X1_39)
% 3.81/1.00      | r1_tarski(k7_relat_1(X0_39,X0_40),k7_relat_1(X1_39,X0_40))
% 3.81/1.00      | ~ v1_relat_1(X1_39) ),
% 3.81/1.00      inference(subtyping,[status(esa)],[c_76]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1919,plain,
% 3.81/1.00      ( r1_tarski(X0_39,X1_39) != iProver_top
% 3.81/1.00      | r1_tarski(k7_relat_1(X0_39,X0_40),k7_relat_1(X1_39,X0_40)) = iProver_top
% 3.81/1.00      | v1_relat_1(X1_39) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_10,negated_conjecture,
% 3.81/1.00      ( v1_relat_1(sK2) ),
% 3.81/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_233,negated_conjecture,
% 3.81/1.00      ( v1_relat_1(sK2) ),
% 3.81/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1921,plain,
% 3.81/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_3,plain,
% 3.81/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.81/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_237,plain,
% 3.81/1.00      ( ~ v1_relat_1(X0_39) | v1_relat_1(k7_relat_1(X0_39,X0_40)) ),
% 3.81/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1915,plain,
% 3.81/1.00      ( v1_relat_1(X0_39) != iProver_top
% 3.81/1.00      | v1_relat_1(k7_relat_1(X0_39,X0_40)) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_5,plain,
% 3.81/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.81/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_236,plain,
% 3.81/1.00      ( ~ v1_relat_1(X0_39)
% 3.81/1.00      | k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40) ),
% 3.81/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1916,plain,
% 3.81/1.00      ( k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40)
% 3.81/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2013,plain,
% 3.81/1.00      ( k2_relat_1(k7_relat_1(k7_relat_1(X0_39,X0_40),X1_40)) = k9_relat_1(k7_relat_1(X0_39,X0_40),X1_40)
% 3.81/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_1915,c_1916]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2069,plain,
% 3.81/1.00      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_40),X1_40)) = k9_relat_1(k7_relat_1(sK2,X0_40),X1_40) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_1921,c_2013]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2012,plain,
% 3.81/1.00      ( k2_relat_1(k7_relat_1(sK2,X0_40)) = k9_relat_1(sK2,X0_40) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_1921,c_1916]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_6,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,X1)
% 3.81/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.81/1.00      | ~ v1_relat_1(X0)
% 3.81/1.00      | ~ v1_relat_1(X1) ),
% 3.81/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_69,plain,
% 3.81/1.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.81/1.00      | ~ r1_tarski(X0,X1)
% 3.81/1.00      | ~ v1_relat_1(X1) ),
% 3.81/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6,c_2,c_0]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_70,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,X1)
% 3.81/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.81/1.00      | ~ v1_relat_1(X1) ),
% 3.81/1.00      inference(renaming,[status(thm)],[c_69]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_231,plain,
% 3.81/1.00      ( ~ r1_tarski(X0_39,X1_39)
% 3.81/1.00      | r1_tarski(k2_relat_1(X0_39),k2_relat_1(X1_39))
% 3.81/1.00      | ~ v1_relat_1(X1_39) ),
% 3.81/1.00      inference(subtyping,[status(esa)],[c_70]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1918,plain,
% 3.81/1.00      ( r1_tarski(X0_39,X1_39) != iProver_top
% 3.81/1.00      | r1_tarski(k2_relat_1(X0_39),k2_relat_1(X1_39)) = iProver_top
% 3.81/1.00      | v1_relat_1(X1_39) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_231]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2212,plain,
% 3.81/1.00      ( r1_tarski(X0_39,k7_relat_1(sK2,X0_40)) != iProver_top
% 3.81/1.00      | r1_tarski(k2_relat_1(X0_39),k9_relat_1(sK2,X0_40)) = iProver_top
% 3.81/1.00      | v1_relat_1(k7_relat_1(sK2,X0_40)) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_2012,c_1918]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_11,plain,
% 3.81/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1983,plain,
% 3.81/1.00      ( v1_relat_1(k7_relat_1(sK2,X0_40)) | ~ v1_relat_1(sK2) ),
% 3.81/1.00      inference(instantiation,[status(thm)],[c_237]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1984,plain,
% 3.81/1.00      ( v1_relat_1(k7_relat_1(sK2,X0_40)) = iProver_top
% 3.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2381,plain,
% 3.81/1.00      ( r1_tarski(k2_relat_1(X0_39),k9_relat_1(sK2,X0_40)) = iProver_top
% 3.81/1.00      | r1_tarski(X0_39,k7_relat_1(sK2,X0_40)) != iProver_top ),
% 3.81/1.00      inference(global_propositional_subsumption,
% 3.81/1.00                [status(thm)],
% 3.81/1.00                [c_2212,c_11,c_1984]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2382,plain,
% 3.81/1.00      ( r1_tarski(X0_39,k7_relat_1(sK2,X0_40)) != iProver_top
% 3.81/1.00      | r1_tarski(k2_relat_1(X0_39),k9_relat_1(sK2,X0_40)) = iProver_top ),
% 3.81/1.00      inference(renaming,[status(thm)],[c_2381]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2390,plain,
% 3.81/1.00      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_40),X1_40),k9_relat_1(sK2,X2_40)) = iProver_top
% 3.81/1.00      | r1_tarski(k7_relat_1(k7_relat_1(sK2,X0_40),X1_40),k7_relat_1(sK2,X2_40)) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_2069,c_2382]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2531,plain,
% 3.81/1.00      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_40),X1_40),k9_relat_1(sK2,X1_40)) = iProver_top
% 3.81/1.00      | r1_tarski(k7_relat_1(sK2,X0_40),sK2) != iProver_top
% 3.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_1919,c_2390]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8,plain,
% 3.81/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.81/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_235,plain,
% 3.81/1.00      ( r1_tarski(k7_relat_1(X0_39,X0_40),X0_39) | ~ v1_relat_1(X0_39) ),
% 3.81/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1982,plain,
% 3.81/1.00      ( r1_tarski(k7_relat_1(sK2,X0_40),sK2) | ~ v1_relat_1(sK2) ),
% 3.81/1.00      inference(instantiation,[status(thm)],[c_235]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1986,plain,
% 3.81/1.00      ( r1_tarski(k7_relat_1(sK2,X0_40),sK2) = iProver_top
% 3.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1982]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_10136,plain,
% 3.81/1.00      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_40),X1_40),k9_relat_1(sK2,X1_40)) = iProver_top ),
% 3.81/1.00      inference(global_propositional_subsumption,
% 3.81/1.00                [status(thm)],
% 3.81/1.00                [c_2531,c_11,c_1986]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_9,negated_conjecture,
% 3.81/1.00      ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
% 3.81/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_234,negated_conjecture,
% 3.81/1.00      ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
% 3.81/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1922,plain,
% 3.81/1.00      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_10141,plain,
% 3.81/1.00      ( $false ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_10136,c_1922]) ).
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  ------                               Statistics
% 3.81/1.00  
% 3.81/1.00  ------ Selected
% 3.81/1.00  
% 3.81/1.00  total_time:                             0.395
% 3.81/1.00  
%------------------------------------------------------------------------------
