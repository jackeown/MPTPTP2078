%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:33 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 500 expanded)
%              Number of clauses        :   77 ( 243 expanded)
%              Number of leaves         :   13 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          :  269 (1256 expanded)
%              Number of equality atoms :   85 ( 201 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f28])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_216,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X1_44)),X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_641,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X1_44)),X1_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_221,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_636,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_8,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_215,plain,
    ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_642,plain,
    ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0_46,X0_44)
    | r2_hidden(X0_46,X1_44)
    | ~ r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_637,plain,
    ( r2_hidden(X0_46,X0_44) != iProver_top
    | r2_hidden(X0_46,X1_44) = iProver_top
    | r1_tarski(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_1610,plain,
    ( r2_hidden(X0_46,X0_44) = iProver_top
    | r2_hidden(X0_46,k7_relat_1(X0_44,X1_44)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_637])).

cnf(c_3120,plain,
    ( r2_hidden(sK0(k7_relat_1(X0_44,X1_44),X2_44),X0_44) = iProver_top
    | r1_tarski(k7_relat_1(X0_44,X1_44),X2_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_1610])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_209,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_648,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_639,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_830,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_639])).

cnf(c_1609,plain,
    ( r2_hidden(X0_46,k2_zfmisc_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0_46,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_637])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_222,plain,
    ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_635,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_2078,plain,
    ( r2_hidden(sK0(X0_44,k2_zfmisc_1(sK1,sK3)),sK4) != iProver_top
    | r1_tarski(X0_44,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1609,c_635])).

cnf(c_4620,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3120,c_2078])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_123,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_124,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_123])).

cnf(c_151,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_124])).

cnf(c_208,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ v1_relat_1(X1_44)
    | v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_151])).

cnf(c_649,plain,
    ( r1_tarski(X0_44,X1_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_1399,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_649])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_217,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_640,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_1494,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1399,c_640])).

cnf(c_4840,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4620,c_1494])).

cnf(c_219,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_638,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) = iProver_top
    | r1_tarski(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | k2_relset_1(X1_44,X2_44,X0_44) = k2_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_644,plain,
    ( k2_relset_1(X0_44,X1_44,X2_44) = k2_relat_1(X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_1087,plain,
    ( k2_relset_1(X0_44,X1_44,X2_44) = k2_relat_1(X2_44)
    | r1_tarski(X2_44,k2_zfmisc_1(X0_44,X1_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_644])).

cnf(c_4850,plain,
    ( k2_relset_1(sK1,sK3,k7_relat_1(sK4,X0_44)) = k2_relat_1(k7_relat_1(sK4,X0_44)) ),
    inference(superposition,[status(thm)],[c_4840,c_1087])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | m1_subset_1(k2_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X2_44)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_643,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X2_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_972,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
    | r1_tarski(k2_relset_1(X1_44,X2_44,X0_44),X2_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_639])).

cnf(c_2493,plain,
    ( r1_tarski(X0_44,k2_zfmisc_1(X1_44,X2_44)) != iProver_top
    | r1_tarski(k2_relset_1(X1_44,X2_44,X0_44),X2_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_972])).

cnf(c_4872,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_44)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4850,c_2493])).

cnf(c_6188,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_44)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4872,c_1494,c_4620])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_211,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | ~ r1_tarski(k2_relat_1(X0_44),X2_44)
    | ~ r1_tarski(k1_relat_1(X0_44),X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_646,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) = iProver_top
    | r1_tarski(k2_relat_1(X0_44),X2_44) != iProver_top
    | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_212,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | k5_relset_1(X1_44,X2_44,X0_44,X3_44) = k7_relat_1(X0_44,X3_44) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_645,plain,
    ( k5_relset_1(X0_44,X1_44,X2_44,X3_44) = k7_relat_1(X2_44,X3_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_1499,plain,
    ( k5_relset_1(sK1,sK3,sK4,X0_44) = k7_relat_1(sK4,X0_44) ),
    inference(superposition,[status(thm)],[c_648,c_645])).

cnf(c_13,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_210,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_647,plain,
    ( m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_1833,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1499,c_647])).

cnf(c_1842,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_1833])).

cnf(c_6197,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6188,c_1842])).

cnf(c_4848,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0_44)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4840,c_649])).

cnf(c_2241,plain,
    ( ~ r1_tarski(X0_44,sK4)
    | v1_relat_1(X0_44)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_4138,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,X0_44),sK4)
    | v1_relat_1(k7_relat_1(sK4,X0_44))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_4140,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_44),sK4) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0_44)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4138])).

cnf(c_4139,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_44),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_4144,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_44),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4139])).

cnf(c_4953,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0_44)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4848,c_1494,c_4140,c_4144])).

cnf(c_6383,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6197,c_4953])).

cnf(c_6385,plain,
    ( v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_6383])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6385,c_1494])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.25/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/0.99  
% 3.25/0.99  ------  iProver source info
% 3.25/0.99  
% 3.25/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.25/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/0.99  git: non_committed_changes: false
% 3.25/0.99  git: last_make_outside_of_git: false
% 3.25/0.99  
% 3.25/0.99  ------ 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options
% 3.25/0.99  
% 3.25/0.99  --out_options                           all
% 3.25/0.99  --tptp_safe_out                         true
% 3.25/0.99  --problem_path                          ""
% 3.25/0.99  --include_path                          ""
% 3.25/0.99  --clausifier                            res/vclausify_rel
% 3.25/0.99  --clausifier_options                    --mode clausify
% 3.25/0.99  --stdin                                 false
% 3.25/0.99  --stats_out                             all
% 3.25/0.99  
% 3.25/0.99  ------ General Options
% 3.25/0.99  
% 3.25/0.99  --fof                                   false
% 3.25/0.99  --time_out_real                         305.
% 3.25/0.99  --time_out_virtual                      -1.
% 3.25/0.99  --symbol_type_check                     false
% 3.25/0.99  --clausify_out                          false
% 3.25/0.99  --sig_cnt_out                           false
% 3.25/0.99  --trig_cnt_out                          false
% 3.25/0.99  --trig_cnt_out_tolerance                1.
% 3.25/0.99  --trig_cnt_out_sk_spl                   false
% 3.25/0.99  --abstr_cl_out                          false
% 3.25/0.99  
% 3.25/0.99  ------ Global Options
% 3.25/0.99  
% 3.25/0.99  --schedule                              default
% 3.25/0.99  --add_important_lit                     false
% 3.25/0.99  --prop_solver_per_cl                    1000
% 3.25/0.99  --min_unsat_core                        false
% 3.25/0.99  --soft_assumptions                      false
% 3.25/0.99  --soft_lemma_size                       3
% 3.25/0.99  --prop_impl_unit_size                   0
% 3.25/0.99  --prop_impl_unit                        []
% 3.25/0.99  --share_sel_clauses                     true
% 3.25/0.99  --reset_solvers                         false
% 3.25/0.99  --bc_imp_inh                            [conj_cone]
% 3.25/0.99  --conj_cone_tolerance                   3.
% 3.25/0.99  --extra_neg_conj                        none
% 3.25/0.99  --large_theory_mode                     true
% 3.25/0.99  --prolific_symb_bound                   200
% 3.25/0.99  --lt_threshold                          2000
% 3.25/0.99  --clause_weak_htbl                      true
% 3.25/0.99  --gc_record_bc_elim                     false
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing Options
% 3.25/0.99  
% 3.25/0.99  --preprocessing_flag                    true
% 3.25/0.99  --time_out_prep_mult                    0.1
% 3.25/0.99  --splitting_mode                        input
% 3.25/0.99  --splitting_grd                         true
% 3.25/0.99  --splitting_cvd                         false
% 3.25/0.99  --splitting_cvd_svl                     false
% 3.25/0.99  --splitting_nvd                         32
% 3.25/0.99  --sub_typing                            true
% 3.25/0.99  --prep_gs_sim                           true
% 3.25/0.99  --prep_unflatten                        true
% 3.25/0.99  --prep_res_sim                          true
% 3.25/0.99  --prep_upred                            true
% 3.25/0.99  --prep_sem_filter                       exhaustive
% 3.25/0.99  --prep_sem_filter_out                   false
% 3.25/0.99  --pred_elim                             true
% 3.25/0.99  --res_sim_input                         true
% 3.25/0.99  --eq_ax_congr_red                       true
% 3.25/0.99  --pure_diseq_elim                       true
% 3.25/0.99  --brand_transform                       false
% 3.25/0.99  --non_eq_to_eq                          false
% 3.25/0.99  --prep_def_merge                        true
% 3.25/0.99  --prep_def_merge_prop_impl              false
% 3.25/0.99  --prep_def_merge_mbd                    true
% 3.25/0.99  --prep_def_merge_tr_red                 false
% 3.25/0.99  --prep_def_merge_tr_cl                  false
% 3.25/0.99  --smt_preprocessing                     true
% 3.25/0.99  --smt_ac_axioms                         fast
% 3.25/0.99  --preprocessed_out                      false
% 3.25/0.99  --preprocessed_stats                    false
% 3.25/0.99  
% 3.25/0.99  ------ Abstraction refinement Options
% 3.25/0.99  
% 3.25/0.99  --abstr_ref                             []
% 3.25/0.99  --abstr_ref_prep                        false
% 3.25/0.99  --abstr_ref_until_sat                   false
% 3.25/0.99  --abstr_ref_sig_restrict                funpre
% 3.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.99  --abstr_ref_under                       []
% 3.25/0.99  
% 3.25/0.99  ------ SAT Options
% 3.25/0.99  
% 3.25/0.99  --sat_mode                              false
% 3.25/0.99  --sat_fm_restart_options                ""
% 3.25/0.99  --sat_gr_def                            false
% 3.25/0.99  --sat_epr_types                         true
% 3.25/0.99  --sat_non_cyclic_types                  false
% 3.25/0.99  --sat_finite_models                     false
% 3.25/0.99  --sat_fm_lemmas                         false
% 3.25/0.99  --sat_fm_prep                           false
% 3.25/0.99  --sat_fm_uc_incr                        true
% 3.25/0.99  --sat_out_model                         small
% 3.25/0.99  --sat_out_clauses                       false
% 3.25/0.99  
% 3.25/0.99  ------ QBF Options
% 3.25/0.99  
% 3.25/0.99  --qbf_mode                              false
% 3.25/0.99  --qbf_elim_univ                         false
% 3.25/0.99  --qbf_dom_inst                          none
% 3.25/0.99  --qbf_dom_pre_inst                      false
% 3.25/0.99  --qbf_sk_in                             false
% 3.25/0.99  --qbf_pred_elim                         true
% 3.25/0.99  --qbf_split                             512
% 3.25/0.99  
% 3.25/0.99  ------ BMC1 Options
% 3.25/0.99  
% 3.25/0.99  --bmc1_incremental                      false
% 3.25/0.99  --bmc1_axioms                           reachable_all
% 3.25/0.99  --bmc1_min_bound                        0
% 3.25/0.99  --bmc1_max_bound                        -1
% 3.25/0.99  --bmc1_max_bound_default                -1
% 3.25/0.99  --bmc1_symbol_reachability              true
% 3.25/0.99  --bmc1_property_lemmas                  false
% 3.25/0.99  --bmc1_k_induction                      false
% 3.25/0.99  --bmc1_non_equiv_states                 false
% 3.25/0.99  --bmc1_deadlock                         false
% 3.25/0.99  --bmc1_ucm                              false
% 3.25/0.99  --bmc1_add_unsat_core                   none
% 3.25/0.99  --bmc1_unsat_core_children              false
% 3.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.99  --bmc1_out_stat                         full
% 3.25/0.99  --bmc1_ground_init                      false
% 3.25/0.99  --bmc1_pre_inst_next_state              false
% 3.25/0.99  --bmc1_pre_inst_state                   false
% 3.25/0.99  --bmc1_pre_inst_reach_state             false
% 3.25/0.99  --bmc1_out_unsat_core                   false
% 3.25/0.99  --bmc1_aig_witness_out                  false
% 3.25/0.99  --bmc1_verbose                          false
% 3.25/0.99  --bmc1_dump_clauses_tptp                false
% 3.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.99  --bmc1_dump_file                        -
% 3.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.99  --bmc1_ucm_extend_mode                  1
% 3.25/0.99  --bmc1_ucm_init_mode                    2
% 3.25/0.99  --bmc1_ucm_cone_mode                    none
% 3.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.99  --bmc1_ucm_relax_model                  4
% 3.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.99  --bmc1_ucm_layered_model                none
% 3.25/0.99  --bmc1_ucm_max_lemma_size               10
% 3.25/0.99  
% 3.25/0.99  ------ AIG Options
% 3.25/0.99  
% 3.25/0.99  --aig_mode                              false
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation Options
% 3.25/0.99  
% 3.25/0.99  --instantiation_flag                    true
% 3.25/0.99  --inst_sos_flag                         false
% 3.25/0.99  --inst_sos_phase                        true
% 3.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel_side                     num_symb
% 3.25/0.99  --inst_solver_per_active                1400
% 3.25/0.99  --inst_solver_calls_frac                1.
% 3.25/0.99  --inst_passive_queue_type               priority_queues
% 3.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.99  --inst_passive_queues_freq              [25;2]
% 3.25/0.99  --inst_dismatching                      true
% 3.25/0.99  --inst_eager_unprocessed_to_passive     true
% 3.25/0.99  --inst_prop_sim_given                   true
% 3.25/0.99  --inst_prop_sim_new                     false
% 3.25/0.99  --inst_subs_new                         false
% 3.25/0.99  --inst_eq_res_simp                      false
% 3.25/0.99  --inst_subs_given                       false
% 3.25/0.99  --inst_orphan_elimination               true
% 3.25/0.99  --inst_learning_loop_flag               true
% 3.25/0.99  --inst_learning_start                   3000
% 3.25/0.99  --inst_learning_factor                  2
% 3.25/0.99  --inst_start_prop_sim_after_learn       3
% 3.25/0.99  --inst_sel_renew                        solver
% 3.25/0.99  --inst_lit_activity_flag                true
% 3.25/0.99  --inst_restr_to_given                   false
% 3.25/0.99  --inst_activity_threshold               500
% 3.25/0.99  --inst_out_proof                        true
% 3.25/0.99  
% 3.25/0.99  ------ Resolution Options
% 3.25/0.99  
% 3.25/0.99  --resolution_flag                       true
% 3.25/0.99  --res_lit_sel                           adaptive
% 3.25/0.99  --res_lit_sel_side                      none
% 3.25/0.99  --res_ordering                          kbo
% 3.25/0.99  --res_to_prop_solver                    active
% 3.25/0.99  --res_prop_simpl_new                    false
% 3.25/0.99  --res_prop_simpl_given                  true
% 3.25/0.99  --res_passive_queue_type                priority_queues
% 3.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.99  --res_passive_queues_freq               [15;5]
% 3.25/0.99  --res_forward_subs                      full
% 3.25/0.99  --res_backward_subs                     full
% 3.25/0.99  --res_forward_subs_resolution           true
% 3.25/0.99  --res_backward_subs_resolution          true
% 3.25/0.99  --res_orphan_elimination                true
% 3.25/0.99  --res_time_limit                        2.
% 3.25/0.99  --res_out_proof                         true
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Options
% 3.25/0.99  
% 3.25/0.99  --superposition_flag                    true
% 3.25/0.99  --sup_passive_queue_type                priority_queues
% 3.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.99  --demod_completeness_check              fast
% 3.25/0.99  --demod_use_ground                      true
% 3.25/0.99  --sup_to_prop_solver                    passive
% 3.25/0.99  --sup_prop_simpl_new                    true
% 3.25/0.99  --sup_prop_simpl_given                  true
% 3.25/0.99  --sup_fun_splitting                     false
% 3.25/0.99  --sup_smt_interval                      50000
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Simplification Setup
% 3.25/0.99  
% 3.25/0.99  --sup_indices_passive                   []
% 3.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_full_bw                           [BwDemod]
% 3.25/0.99  --sup_immed_triv                        [TrivRules]
% 3.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_immed_bw_main                     []
% 3.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  
% 3.25/0.99  ------ Combination Options
% 3.25/0.99  
% 3.25/0.99  --comb_res_mult                         3
% 3.25/0.99  --comb_sup_mult                         2
% 3.25/0.99  --comb_inst_mult                        10
% 3.25/0.99  
% 3.25/0.99  ------ Debug Options
% 3.25/0.99  
% 3.25/0.99  --dbg_backtrace                         false
% 3.25/0.99  --dbg_dump_prop_clauses                 false
% 3.25/0.99  --dbg_dump_prop_clauses_file            -
% 3.25/0.99  --dbg_out_stat                          false
% 3.25/0.99  ------ Parsing...
% 3.25/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/0.99  ------ Proving...
% 3.25/0.99  ------ Problem Properties 
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  clauses                                 15
% 3.25/0.99  conjectures                             2
% 3.25/0.99  EPR                                     2
% 3.25/0.99  Horn                                    14
% 3.25/0.99  unary                                   3
% 3.25/0.99  binary                                  9
% 3.25/0.99  lits                                    31
% 3.25/0.99  lits eq                                 2
% 3.25/0.99  fd_pure                                 0
% 3.25/0.99  fd_pseudo                               0
% 3.25/0.99  fd_cond                                 0
% 3.25/0.99  fd_pseudo_cond                          0
% 3.25/0.99  AC symbols                              0
% 3.25/0.99  
% 3.25/0.99  ------ Schedule dynamic 5 is on 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  ------ 
% 3.25/0.99  Current options:
% 3.25/0.99  ------ 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options
% 3.25/0.99  
% 3.25/0.99  --out_options                           all
% 3.25/0.99  --tptp_safe_out                         true
% 3.25/0.99  --problem_path                          ""
% 3.25/0.99  --include_path                          ""
% 3.25/0.99  --clausifier                            res/vclausify_rel
% 3.25/0.99  --clausifier_options                    --mode clausify
% 3.25/0.99  --stdin                                 false
% 3.25/0.99  --stats_out                             all
% 3.25/0.99  
% 3.25/0.99  ------ General Options
% 3.25/0.99  
% 3.25/0.99  --fof                                   false
% 3.25/0.99  --time_out_real                         305.
% 3.25/0.99  --time_out_virtual                      -1.
% 3.25/0.99  --symbol_type_check                     false
% 3.25/0.99  --clausify_out                          false
% 3.25/0.99  --sig_cnt_out                           false
% 3.25/0.99  --trig_cnt_out                          false
% 3.25/0.99  --trig_cnt_out_tolerance                1.
% 3.25/0.99  --trig_cnt_out_sk_spl                   false
% 3.25/0.99  --abstr_cl_out                          false
% 3.25/0.99  
% 3.25/0.99  ------ Global Options
% 3.25/0.99  
% 3.25/0.99  --schedule                              default
% 3.25/0.99  --add_important_lit                     false
% 3.25/0.99  --prop_solver_per_cl                    1000
% 3.25/0.99  --min_unsat_core                        false
% 3.25/0.99  --soft_assumptions                      false
% 3.25/0.99  --soft_lemma_size                       3
% 3.25/0.99  --prop_impl_unit_size                   0
% 3.25/0.99  --prop_impl_unit                        []
% 3.25/0.99  --share_sel_clauses                     true
% 3.25/0.99  --reset_solvers                         false
% 3.25/0.99  --bc_imp_inh                            [conj_cone]
% 3.25/0.99  --conj_cone_tolerance                   3.
% 3.25/0.99  --extra_neg_conj                        none
% 3.25/0.99  --large_theory_mode                     true
% 3.25/0.99  --prolific_symb_bound                   200
% 3.25/0.99  --lt_threshold                          2000
% 3.25/0.99  --clause_weak_htbl                      true
% 3.25/0.99  --gc_record_bc_elim                     false
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing Options
% 3.25/0.99  
% 3.25/0.99  --preprocessing_flag                    true
% 3.25/0.99  --time_out_prep_mult                    0.1
% 3.25/0.99  --splitting_mode                        input
% 3.25/0.99  --splitting_grd                         true
% 3.25/0.99  --splitting_cvd                         false
% 3.25/0.99  --splitting_cvd_svl                     false
% 3.25/0.99  --splitting_nvd                         32
% 3.25/0.99  --sub_typing                            true
% 3.25/0.99  --prep_gs_sim                           true
% 3.25/0.99  --prep_unflatten                        true
% 3.25/0.99  --prep_res_sim                          true
% 3.25/0.99  --prep_upred                            true
% 3.25/0.99  --prep_sem_filter                       exhaustive
% 3.25/0.99  --prep_sem_filter_out                   false
% 3.25/0.99  --pred_elim                             true
% 3.25/0.99  --res_sim_input                         true
% 3.25/0.99  --eq_ax_congr_red                       true
% 3.25/0.99  --pure_diseq_elim                       true
% 3.25/0.99  --brand_transform                       false
% 3.25/0.99  --non_eq_to_eq                          false
% 3.25/0.99  --prep_def_merge                        true
% 3.25/0.99  --prep_def_merge_prop_impl              false
% 3.25/0.99  --prep_def_merge_mbd                    true
% 3.25/0.99  --prep_def_merge_tr_red                 false
% 3.25/0.99  --prep_def_merge_tr_cl                  false
% 3.25/0.99  --smt_preprocessing                     true
% 3.25/0.99  --smt_ac_axioms                         fast
% 3.25/0.99  --preprocessed_out                      false
% 3.25/0.99  --preprocessed_stats                    false
% 3.25/0.99  
% 3.25/0.99  ------ Abstraction refinement Options
% 3.25/0.99  
% 3.25/0.99  --abstr_ref                             []
% 3.25/0.99  --abstr_ref_prep                        false
% 3.25/0.99  --abstr_ref_until_sat                   false
% 3.25/0.99  --abstr_ref_sig_restrict                funpre
% 3.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.99  --abstr_ref_under                       []
% 3.25/0.99  
% 3.25/0.99  ------ SAT Options
% 3.25/0.99  
% 3.25/0.99  --sat_mode                              false
% 3.25/0.99  --sat_fm_restart_options                ""
% 3.25/0.99  --sat_gr_def                            false
% 3.25/0.99  --sat_epr_types                         true
% 3.25/0.99  --sat_non_cyclic_types                  false
% 3.25/0.99  --sat_finite_models                     false
% 3.25/0.99  --sat_fm_lemmas                         false
% 3.25/0.99  --sat_fm_prep                           false
% 3.25/0.99  --sat_fm_uc_incr                        true
% 3.25/0.99  --sat_out_model                         small
% 3.25/0.99  --sat_out_clauses                       false
% 3.25/0.99  
% 3.25/0.99  ------ QBF Options
% 3.25/0.99  
% 3.25/0.99  --qbf_mode                              false
% 3.25/0.99  --qbf_elim_univ                         false
% 3.25/0.99  --qbf_dom_inst                          none
% 3.25/0.99  --qbf_dom_pre_inst                      false
% 3.25/0.99  --qbf_sk_in                             false
% 3.25/0.99  --qbf_pred_elim                         true
% 3.25/0.99  --qbf_split                             512
% 3.25/0.99  
% 3.25/0.99  ------ BMC1 Options
% 3.25/0.99  
% 3.25/0.99  --bmc1_incremental                      false
% 3.25/0.99  --bmc1_axioms                           reachable_all
% 3.25/0.99  --bmc1_min_bound                        0
% 3.25/0.99  --bmc1_max_bound                        -1
% 3.25/0.99  --bmc1_max_bound_default                -1
% 3.25/0.99  --bmc1_symbol_reachability              true
% 3.25/0.99  --bmc1_property_lemmas                  false
% 3.25/0.99  --bmc1_k_induction                      false
% 3.25/0.99  --bmc1_non_equiv_states                 false
% 3.25/0.99  --bmc1_deadlock                         false
% 3.25/0.99  --bmc1_ucm                              false
% 3.25/0.99  --bmc1_add_unsat_core                   none
% 3.25/0.99  --bmc1_unsat_core_children              false
% 3.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.99  --bmc1_out_stat                         full
% 3.25/0.99  --bmc1_ground_init                      false
% 3.25/0.99  --bmc1_pre_inst_next_state              false
% 3.25/0.99  --bmc1_pre_inst_state                   false
% 3.25/0.99  --bmc1_pre_inst_reach_state             false
% 3.25/0.99  --bmc1_out_unsat_core                   false
% 3.25/0.99  --bmc1_aig_witness_out                  false
% 3.25/0.99  --bmc1_verbose                          false
% 3.25/0.99  --bmc1_dump_clauses_tptp                false
% 3.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.99  --bmc1_dump_file                        -
% 3.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.99  --bmc1_ucm_extend_mode                  1
% 3.25/0.99  --bmc1_ucm_init_mode                    2
% 3.25/0.99  --bmc1_ucm_cone_mode                    none
% 3.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.99  --bmc1_ucm_relax_model                  4
% 3.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.99  --bmc1_ucm_layered_model                none
% 3.25/0.99  --bmc1_ucm_max_lemma_size               10
% 3.25/0.99  
% 3.25/0.99  ------ AIG Options
% 3.25/0.99  
% 3.25/0.99  --aig_mode                              false
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation Options
% 3.25/0.99  
% 3.25/0.99  --instantiation_flag                    true
% 3.25/0.99  --inst_sos_flag                         false
% 3.25/0.99  --inst_sos_phase                        true
% 3.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel_side                     none
% 3.25/0.99  --inst_solver_per_active                1400
% 3.25/0.99  --inst_solver_calls_frac                1.
% 3.25/0.99  --inst_passive_queue_type               priority_queues
% 3.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.99  --inst_passive_queues_freq              [25;2]
% 3.25/0.99  --inst_dismatching                      true
% 3.25/0.99  --inst_eager_unprocessed_to_passive     true
% 3.25/0.99  --inst_prop_sim_given                   true
% 3.25/0.99  --inst_prop_sim_new                     false
% 3.25/0.99  --inst_subs_new                         false
% 3.25/0.99  --inst_eq_res_simp                      false
% 3.25/0.99  --inst_subs_given                       false
% 3.25/0.99  --inst_orphan_elimination               true
% 3.25/0.99  --inst_learning_loop_flag               true
% 3.25/0.99  --inst_learning_start                   3000
% 3.25/0.99  --inst_learning_factor                  2
% 3.25/0.99  --inst_start_prop_sim_after_learn       3
% 3.25/0.99  --inst_sel_renew                        solver
% 3.25/0.99  --inst_lit_activity_flag                true
% 3.25/0.99  --inst_restr_to_given                   false
% 3.25/0.99  --inst_activity_threshold               500
% 3.25/0.99  --inst_out_proof                        true
% 3.25/0.99  
% 3.25/0.99  ------ Resolution Options
% 3.25/0.99  
% 3.25/0.99  --resolution_flag                       false
% 3.25/0.99  --res_lit_sel                           adaptive
% 3.25/0.99  --res_lit_sel_side                      none
% 3.25/0.99  --res_ordering                          kbo
% 3.25/0.99  --res_to_prop_solver                    active
% 3.25/0.99  --res_prop_simpl_new                    false
% 3.25/0.99  --res_prop_simpl_given                  true
% 3.25/0.99  --res_passive_queue_type                priority_queues
% 3.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.99  --res_passive_queues_freq               [15;5]
% 3.25/0.99  --res_forward_subs                      full
% 3.25/0.99  --res_backward_subs                     full
% 3.25/0.99  --res_forward_subs_resolution           true
% 3.25/0.99  --res_backward_subs_resolution          true
% 3.25/0.99  --res_orphan_elimination                true
% 3.25/0.99  --res_time_limit                        2.
% 3.25/0.99  --res_out_proof                         true
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Options
% 3.25/0.99  
% 3.25/0.99  --superposition_flag                    true
% 3.25/0.99  --sup_passive_queue_type                priority_queues
% 3.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.99  --demod_completeness_check              fast
% 3.25/0.99  --demod_use_ground                      true
% 3.25/0.99  --sup_to_prop_solver                    passive
% 3.25/0.99  --sup_prop_simpl_new                    true
% 3.25/0.99  --sup_prop_simpl_given                  true
% 3.25/0.99  --sup_fun_splitting                     false
% 3.25/0.99  --sup_smt_interval                      50000
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Simplification Setup
% 3.25/0.99  
% 3.25/0.99  --sup_indices_passive                   []
% 3.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_full_bw                           [BwDemod]
% 3.25/0.99  --sup_immed_triv                        [TrivRules]
% 3.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_immed_bw_main                     []
% 3.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  
% 3.25/0.99  ------ Combination Options
% 3.25/0.99  
% 3.25/0.99  --comb_res_mult                         3
% 3.25/0.99  --comb_sup_mult                         2
% 3.25/0.99  --comb_inst_mult                        10
% 3.25/0.99  
% 3.25/0.99  ------ Debug Options
% 3.25/0.99  
% 3.25/0.99  --dbg_backtrace                         false
% 3.25/0.99  --dbg_dump_prop_clauses                 false
% 3.25/0.99  --dbg_dump_prop_clauses_file            -
% 3.25/0.99  --dbg_out_stat                          false
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  ------ Proving...
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  % SZS status Theorem for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  fof(f5,axiom,(
% 3.25/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f15,plain,(
% 3.25/0.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.25/0.99    inference(ennf_transformation,[],[f5])).
% 3.25/0.99  
% 3.25/0.99  fof(f37,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f15])).
% 3.25/0.99  
% 3.25/0.99  fof(f1,axiom,(
% 3.25/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f13,plain,(
% 3.25/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f1])).
% 3.25/0.99  
% 3.25/0.99  fof(f23,plain,(
% 3.25/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/0.99    inference(nnf_transformation,[],[f13])).
% 3.25/0.99  
% 3.25/0.99  fof(f24,plain,(
% 3.25/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/0.99    inference(rectify,[],[f23])).
% 3.25/0.99  
% 3.25/0.99  fof(f25,plain,(
% 3.25/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f26,plain,(
% 3.25/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.25/0.99  
% 3.25/0.99  fof(f31,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f26])).
% 3.25/0.99  
% 3.25/0.99  fof(f6,axiom,(
% 3.25/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f16,plain,(
% 3.25/0.99    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.25/0.99    inference(ennf_transformation,[],[f6])).
% 3.25/0.99  
% 3.25/0.99  fof(f38,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f16])).
% 3.25/0.99  
% 3.25/0.99  fof(f30,plain,(
% 3.25/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f26])).
% 3.25/0.99  
% 3.25/0.99  fof(f11,conjecture,(
% 3.25/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f12,negated_conjecture,(
% 3.25/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.25/0.99    inference(negated_conjecture,[],[f11])).
% 3.25/0.99  
% 3.25/0.99  fof(f22,plain,(
% 3.25/0.99    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.25/0.99    inference(ennf_transformation,[],[f12])).
% 3.25/0.99  
% 3.25/0.99  fof(f28,plain,(
% 3.25/0.99    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))))),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f29,plain,(
% 3.25/0.99    ~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 3.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f28])).
% 3.25/0.99  
% 3.25/0.99  fof(f43,plain,(
% 3.25/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 3.25/0.99    inference(cnf_transformation,[],[f29])).
% 3.25/0.99  
% 3.25/0.99  fof(f2,axiom,(
% 3.25/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f27,plain,(
% 3.25/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.25/0.99    inference(nnf_transformation,[],[f2])).
% 3.25/0.99  
% 3.25/0.99  fof(f33,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f27])).
% 3.25/0.99  
% 3.25/0.99  fof(f32,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f26])).
% 3.25/0.99  
% 3.25/0.99  fof(f3,axiom,(
% 3.25/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f14,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.25/0.99    inference(ennf_transformation,[],[f3])).
% 3.25/0.99  
% 3.25/0.99  fof(f35,plain,(
% 3.25/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f14])).
% 3.25/0.99  
% 3.25/0.99  fof(f34,plain,(
% 3.25/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f27])).
% 3.25/0.99  
% 3.25/0.99  fof(f4,axiom,(
% 3.25/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f36,plain,(
% 3.25/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f4])).
% 3.25/0.99  
% 3.25/0.99  fof(f8,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f18,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(ennf_transformation,[],[f8])).
% 3.25/0.99  
% 3.25/0.99  fof(f40,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f18])).
% 3.25/0.99  
% 3.25/0.99  fof(f7,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f17,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(ennf_transformation,[],[f7])).
% 3.25/0.99  
% 3.25/0.99  fof(f39,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f17])).
% 3.25/0.99  
% 3.25/0.99  fof(f10,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f20,plain,(
% 3.25/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.25/0.99    inference(ennf_transformation,[],[f10])).
% 3.25/0.99  
% 3.25/0.99  fof(f21,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.25/0.99    inference(flattening,[],[f20])).
% 3.25/0.99  
% 3.25/0.99  fof(f42,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f21])).
% 3.25/0.99  
% 3.25/0.99  fof(f9,axiom,(
% 3.25/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f19,plain,(
% 3.25/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(ennf_transformation,[],[f9])).
% 3.25/0.99  
% 3.25/0.99  fof(f41,plain,(
% 3.25/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f19])).
% 3.25/0.99  
% 3.25/0.99  fof(f44,plain,(
% 3.25/0.99    ~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.25/0.99    inference(cnf_transformation,[],[f29])).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7,plain,
% 3.25/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_216,plain,
% 3.25/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X1_44)),X1_44)
% 3.25/0.99      | ~ v1_relat_1(X0_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_641,plain,
% 3.25/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X1_44)),X1_44) = iProver_top
% 3.25/0.99      | v1_relat_1(X0_44) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1,plain,
% 3.25/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.25/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_221,plain,
% 3.25/0.99      ( r2_hidden(sK0(X0_44,X1_44),X0_44) | r1_tarski(X0_44,X1_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_636,plain,
% 3.25/0.99      ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
% 3.25/0.99      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_8,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_215,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) | ~ v1_relat_1(X0_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_642,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) = iProver_top
% 3.25/0.99      | v1_relat_1(X0_44) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2,plain,
% 3.25/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_220,plain,
% 3.25/0.99      ( ~ r2_hidden(X0_46,X0_44)
% 3.25/0.99      | r2_hidden(X0_46,X1_44)
% 3.25/0.99      | ~ r1_tarski(X0_44,X1_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_637,plain,
% 3.25/0.99      ( r2_hidden(X0_46,X0_44) != iProver_top
% 3.25/0.99      | r2_hidden(X0_46,X1_44) = iProver_top
% 3.25/0.99      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1610,plain,
% 3.25/0.99      ( r2_hidden(X0_46,X0_44) = iProver_top
% 3.25/0.99      | r2_hidden(X0_46,k7_relat_1(X0_44,X1_44)) != iProver_top
% 3.25/0.99      | v1_relat_1(X0_44) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_642,c_637]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3120,plain,
% 3.25/0.99      ( r2_hidden(sK0(k7_relat_1(X0_44,X1_44),X2_44),X0_44) = iProver_top
% 3.25/0.99      | r1_tarski(k7_relat_1(X0_44,X1_44),X2_44) = iProver_top
% 3.25/0.99      | v1_relat_1(X0_44) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_636,c_1610]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_14,negated_conjecture,
% 3.25/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.25/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_209,negated_conjecture,
% 3.25/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_648,plain,
% 3.25/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.25/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_218,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.25/0.99      | r1_tarski(X0_44,X1_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_639,plain,
% 3.25/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 3.25/0.99      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_830,plain,
% 3.25/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_648,c_639]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1609,plain,
% 3.25/0.99      ( r2_hidden(X0_46,k2_zfmisc_1(sK1,sK3)) = iProver_top
% 3.25/0.99      | r2_hidden(X0_46,sK4) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_830,c_637]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_0,plain,
% 3.25/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.25/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_222,plain,
% 3.25/0.99      ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44) | r1_tarski(X0_44,X1_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_635,plain,
% 3.25/0.99      ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
% 3.25/0.99      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2078,plain,
% 3.25/0.99      ( r2_hidden(sK0(X0_44,k2_zfmisc_1(sK1,sK3)),sK4) != iProver_top
% 3.25/0.99      | r1_tarski(X0_44,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_1609,c_635]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4620,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) = iProver_top
% 3.25/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_3120,c_2078]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.25/0.99      | ~ v1_relat_1(X1)
% 3.25/0.99      | v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.25/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_123,plain,
% 3.25/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.25/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_124,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_123]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_151,plain,
% 3.25/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.25/0.99      inference(bin_hyper_res,[status(thm)],[c_5,c_124]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_208,plain,
% 3.25/0.99      ( ~ r1_tarski(X0_44,X1_44)
% 3.25/0.99      | ~ v1_relat_1(X1_44)
% 3.25/0.99      | v1_relat_1(X0_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_151]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_649,plain,
% 3.25/0.99      ( r1_tarski(X0_44,X1_44) != iProver_top
% 3.25/0.99      | v1_relat_1(X1_44) != iProver_top
% 3.25/0.99      | v1_relat_1(X0_44) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1399,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK3)) != iProver_top
% 3.25/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_830,c_649]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_217,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_640,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1494,plain,
% 3.25/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.25/0.99      inference(forward_subsumption_resolution,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_1399,c_640]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4840,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_4620,c_1494]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_219,plain,
% 3.25/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.25/0.99      | ~ r1_tarski(X0_44,X1_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_638,plain,
% 3.25/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) = iProver_top
% 3.25/0.99      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_10,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_213,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 3.25/0.99      | k2_relset_1(X1_44,X2_44,X0_44) = k2_relat_1(X0_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_644,plain,
% 3.25/0.99      ( k2_relset_1(X0_44,X1_44,X2_44) = k2_relat_1(X2_44)
% 3.25/0.99      | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1087,plain,
% 3.25/0.99      ( k2_relset_1(X0_44,X1_44,X2_44) = k2_relat_1(X2_44)
% 3.25/0.99      | r1_tarski(X2_44,k2_zfmisc_1(X0_44,X1_44)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_638,c_644]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4850,plain,
% 3.25/0.99      ( k2_relset_1(sK1,sK3,k7_relat_1(sK4,X0_44)) = k2_relat_1(k7_relat_1(sK4,X0_44)) ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_4840,c_1087]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_9,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.25/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_214,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 3.25/0.99      | m1_subset_1(k2_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X2_44)) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_643,plain,
% 3.25/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
% 3.25/0.99      | m1_subset_1(k2_relset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X2_44)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_972,plain,
% 3.25/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
% 3.25/0.99      | r1_tarski(k2_relset_1(X1_44,X2_44,X0_44),X2_44) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_643,c_639]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2493,plain,
% 3.25/0.99      ( r1_tarski(X0_44,k2_zfmisc_1(X1_44,X2_44)) != iProver_top
% 3.25/0.99      | r1_tarski(k2_relset_1(X1_44,X2_44,X0_44),X2_44) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_638,c_972]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4872,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) != iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_44)),sK3) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_4850,c_2493]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6188,plain,
% 3.25/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_44)),sK3) = iProver_top ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_4872,c_1494,c_4620]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_12,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.25/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.25/0.99      | ~ v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_211,plain,
% 3.25/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 3.25/0.99      | ~ r1_tarski(k2_relat_1(X0_44),X2_44)
% 3.25/0.99      | ~ r1_tarski(k1_relat_1(X0_44),X1_44)
% 3.25/0.99      | ~ v1_relat_1(X0_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_646,plain,
% 3.25/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) = iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(X0_44),X2_44) != iProver_top
% 3.25/0.99      | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top
% 3.25/0.99      | v1_relat_1(X0_44) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_11,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.25/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_212,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 3.25/0.99      | k5_relset_1(X1_44,X2_44,X0_44,X3_44) = k7_relat_1(X0_44,X3_44) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_645,plain,
% 3.25/0.99      ( k5_relset_1(X0_44,X1_44,X2_44,X3_44) = k7_relat_1(X2_44,X3_44)
% 3.25/0.99      | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1499,plain,
% 3.25/0.99      ( k5_relset_1(sK1,sK3,sK4,X0_44) = k7_relat_1(sK4,X0_44) ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_648,c_645]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_13,negated_conjecture,
% 3.25/0.99      ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.25/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_210,negated_conjecture,
% 3.25/0.99      ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_647,plain,
% 3.25/0.99      ( m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1833,plain,
% 3.25/0.99      ( m1_subset_1(k7_relat_1(sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_1499,c_647]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1842,plain,
% 3.25/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
% 3.25/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_646,c_1833]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6197,plain,
% 3.25/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_6188,c_1842]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4848,plain,
% 3.25/0.99      ( v1_relat_1(k7_relat_1(sK4,X0_44)) = iProver_top
% 3.25/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK3)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_4840,c_649]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2241,plain,
% 3.25/0.99      ( ~ r1_tarski(X0_44,sK4) | v1_relat_1(X0_44) | ~ v1_relat_1(sK4) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_208]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4138,plain,
% 3.25/0.99      ( ~ r1_tarski(k7_relat_1(sK4,X0_44),sK4)
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK4,X0_44))
% 3.25/0.99      | ~ v1_relat_1(sK4) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2241]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4140,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(sK4,X0_44),sK4) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK4,X0_44)) = iProver_top
% 3.25/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_4138]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4139,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(sK4,X0_44),sK4) | ~ v1_relat_1(sK4) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_215]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4144,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(sK4,X0_44),sK4) = iProver_top
% 3.25/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_4139]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4953,plain,
% 3.25/0.99      ( v1_relat_1(k7_relat_1(sK4,X0_44)) = iProver_top ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_4848,c_1494,c_4140,c_4144]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6383,plain,
% 3.25/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top ),
% 3.25/0.99      inference(forward_subsumption_resolution,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_6197,c_4953]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6385,plain,
% 3.25/0.99      ( v1_relat_1(sK4) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_641,c_6383]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(contradiction,plain,
% 3.25/0.99      ( $false ),
% 3.25/0.99      inference(minisat,[status(thm)],[c_6385,c_1494]) ).
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  ------                               Statistics
% 3.25/0.99  
% 3.25/0.99  ------ General
% 3.25/0.99  
% 3.25/0.99  abstr_ref_over_cycles:                  0
% 3.25/0.99  abstr_ref_under_cycles:                 0
% 3.25/0.99  gc_basic_clause_elim:                   0
% 3.25/0.99  forced_gc_time:                         0
% 3.25/0.99  parsing_time:                           0.009
% 3.25/0.99  unif_index_cands_time:                  0.
% 3.25/0.99  unif_index_add_time:                    0.
% 3.25/0.99  orderings_time:                         0.
% 3.25/0.99  out_proof_time:                         0.007
% 3.25/0.99  total_time:                             0.232
% 3.25/0.99  num_of_symbols:                         50
% 3.25/0.99  num_of_terms:                           7859
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing
% 3.25/0.99  
% 3.25/0.99  num_of_splits:                          0
% 3.25/0.99  num_of_split_atoms:                     0
% 3.25/0.99  num_of_reused_defs:                     0
% 3.25/0.99  num_eq_ax_congr_red:                    20
% 3.25/0.99  num_of_sem_filtered_clauses:            1
% 3.25/0.99  num_of_subtypes:                        3
% 3.25/0.99  monotx_restored_types:                  0
% 3.25/0.99  sat_num_of_epr_types:                   0
% 3.25/0.99  sat_num_of_non_cyclic_types:            0
% 3.25/0.99  sat_guarded_non_collapsed_types:        0
% 3.25/0.99  num_pure_diseq_elim:                    0
% 3.25/0.99  simp_replaced_by:                       0
% 3.25/0.99  res_preprocessed:                       70
% 3.25/0.99  prep_upred:                             0
% 3.25/0.99  prep_unflattend:                        0
% 3.25/0.99  smt_new_axioms:                         0
% 3.25/0.99  pred_elim_cands:                        4
% 3.25/0.99  pred_elim:                              0
% 3.25/0.99  pred_elim_cl:                           0
% 3.25/0.99  pred_elim_cycles:                       1
% 3.25/0.99  merged_defs:                            6
% 3.25/0.99  merged_defs_ncl:                        0
% 3.25/0.99  bin_hyper_res:                          7
% 3.25/0.99  prep_cycles:                            3
% 3.25/0.99  pred_elim_time:                         0.
% 3.25/0.99  splitting_time:                         0.
% 3.25/0.99  sem_filter_time:                        0.
% 3.25/0.99  monotx_time:                            0.
% 3.25/0.99  subtype_inf_time:                       0.
% 3.25/0.99  
% 3.25/0.99  ------ Problem properties
% 3.25/0.99  
% 3.25/0.99  clauses:                                15
% 3.25/0.99  conjectures:                            2
% 3.25/0.99  epr:                                    2
% 3.25/0.99  horn:                                   14
% 3.25/0.99  ground:                                 2
% 3.25/0.99  unary:                                  3
% 3.25/0.99  binary:                                 9
% 3.25/0.99  lits:                                   31
% 3.25/0.99  lits_eq:                                2
% 3.25/0.99  fd_pure:                                0
% 3.25/0.99  fd_pseudo:                              0
% 3.25/0.99  fd_cond:                                0
% 3.25/0.99  fd_pseudo_cond:                         0
% 3.25/0.99  ac_symbols:                             0
% 3.25/0.99  
% 3.25/0.99  ------ Propositional Solver
% 3.25/0.99  
% 3.25/0.99  prop_solver_calls:                      26
% 3.25/0.99  prop_fast_solver_calls:                 477
% 3.25/0.99  smt_solver_calls:                       0
% 3.25/0.99  smt_fast_solver_calls:                  0
% 3.25/0.99  prop_num_of_clauses:                    2871
% 3.25/0.99  prop_preprocess_simplified:             5024
% 3.25/0.99  prop_fo_subsumed:                       9
% 3.25/0.99  prop_solver_time:                       0.
% 3.25/0.99  smt_solver_time:                        0.
% 3.25/0.99  smt_fast_solver_time:                   0.
% 3.25/0.99  prop_fast_solver_time:                  0.
% 3.25/0.99  prop_unsat_core_time:                   0.
% 3.25/0.99  
% 3.25/0.99  ------ QBF
% 3.25/0.99  
% 3.25/0.99  qbf_q_res:                              0
% 3.25/0.99  qbf_num_tautologies:                    0
% 3.25/0.99  qbf_prep_cycles:                        0
% 3.25/0.99  
% 3.25/0.99  ------ BMC1
% 3.25/0.99  
% 3.25/0.99  bmc1_current_bound:                     -1
% 3.25/0.99  bmc1_last_solved_bound:                 -1
% 3.25/0.99  bmc1_unsat_core_size:                   -1
% 3.25/0.99  bmc1_unsat_core_parents_size:           -1
% 3.25/0.99  bmc1_merge_next_fun:                    0
% 3.25/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation
% 3.25/0.99  
% 3.25/0.99  inst_num_of_clauses:                    686
% 3.25/0.99  inst_num_in_passive:                    129
% 3.25/0.99  inst_num_in_active:                     332
% 3.25/0.99  inst_num_in_unprocessed:                225
% 3.25/0.99  inst_num_of_loops:                      410
% 3.25/0.99  inst_num_of_learning_restarts:          0
% 3.25/0.99  inst_num_moves_active_passive:          74
% 3.25/0.99  inst_lit_activity:                      0
% 3.25/0.99  inst_lit_activity_moves:                0
% 3.25/0.99  inst_num_tautologies:                   0
% 3.25/0.99  inst_num_prop_implied:                  0
% 3.25/0.99  inst_num_existing_simplified:           0
% 3.25/0.99  inst_num_eq_res_simplified:             0
% 3.25/0.99  inst_num_child_elim:                    0
% 3.25/0.99  inst_num_of_dismatching_blockings:      353
% 3.25/0.99  inst_num_of_non_proper_insts:           703
% 3.25/0.99  inst_num_of_duplicates:                 0
% 3.25/0.99  inst_inst_num_from_inst_to_res:         0
% 3.25/0.99  inst_dismatching_checking_time:         0.
% 3.25/0.99  
% 3.25/0.99  ------ Resolution
% 3.25/0.99  
% 3.25/0.99  res_num_of_clauses:                     0
% 3.25/0.99  res_num_in_passive:                     0
% 3.25/0.99  res_num_in_active:                      0
% 3.25/0.99  res_num_of_loops:                       73
% 3.25/0.99  res_forward_subset_subsumed:            55
% 3.25/0.99  res_backward_subset_subsumed:           2
% 3.25/0.99  res_forward_subsumed:                   0
% 3.25/0.99  res_backward_subsumed:                  0
% 3.25/0.99  res_forward_subsumption_resolution:     0
% 3.25/0.99  res_backward_subsumption_resolution:    0
% 3.25/0.99  res_clause_to_clause_subsumption:       419
% 3.25/0.99  res_orphan_elimination:                 0
% 3.25/0.99  res_tautology_del:                      56
% 3.25/0.99  res_num_eq_res_simplified:              0
% 3.25/0.99  res_num_sel_changes:                    0
% 3.25/0.99  res_moves_from_active_to_pass:          0
% 3.25/0.99  
% 3.25/0.99  ------ Superposition
% 3.25/0.99  
% 3.25/0.99  sup_time_total:                         0.
% 3.25/0.99  sup_time_generating:                    0.
% 3.25/0.99  sup_time_sim_full:                      0.
% 3.25/0.99  sup_time_sim_immed:                     0.
% 3.25/0.99  
% 3.25/0.99  sup_num_of_clauses:                     140
% 3.25/0.99  sup_num_in_active:                      79
% 3.25/0.99  sup_num_in_passive:                     61
% 3.25/0.99  sup_num_of_loops:                       80
% 3.25/0.99  sup_fw_superposition:                   67
% 3.25/0.99  sup_bw_superposition:                   88
% 3.25/0.99  sup_immediate_simplified:               6
% 3.25/0.99  sup_given_eliminated:                   0
% 3.25/0.99  comparisons_done:                       0
% 3.25/0.99  comparisons_avoided:                    0
% 3.25/0.99  
% 3.25/0.99  ------ Simplifications
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  sim_fw_subset_subsumed:                 1
% 3.25/0.99  sim_bw_subset_subsumed:                 0
% 3.25/0.99  sim_fw_subsumed:                        1
% 3.25/0.99  sim_bw_subsumed:                        0
% 3.25/0.99  sim_fw_subsumption_res:                 3
% 3.25/0.99  sim_bw_subsumption_res:                 0
% 3.25/0.99  sim_tautology_del:                      4
% 3.25/0.99  sim_eq_tautology_del:                   0
% 3.25/0.99  sim_eq_res_simp:                        0
% 3.25/0.99  sim_fw_demodulated:                     3
% 3.25/0.99  sim_bw_demodulated:                     2
% 3.25/0.99  sim_light_normalised:                   2
% 3.25/0.99  sim_joinable_taut:                      0
% 3.25/0.99  sim_joinable_simp:                      0
% 3.25/0.99  sim_ac_normalised:                      0
% 3.25/0.99  sim_smt_subsumption:                    0
% 3.25/0.99  
%------------------------------------------------------------------------------
