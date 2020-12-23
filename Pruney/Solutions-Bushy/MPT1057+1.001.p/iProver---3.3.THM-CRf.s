%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1057+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:48 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   63 (  88 expanded)
%              Number of clauses        :   38 (  41 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  127 ( 212 expanded)
%              Number of equality atoms :   68 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X2,X1)
         => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
     => ( k9_relat_1(X0,sK2) != k9_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(sK2,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(X2,X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(sK2,sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).

fof(f24,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_86,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_86])).

cnf(c_95,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_87])).

cnf(c_96,plain,
    ( k9_relat_1(k6_relat_1(X0),sK2) = sK2
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_95])).

cnf(c_139,plain,
    ( k1_zfmisc_1(X0_41) != k1_zfmisc_1(sK1)
    | k9_relat_1(k6_relat_1(X0_41),sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_96])).

cnf(c_293,plain,
    ( k9_relat_1(k6_relat_1(sK1),sK2) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_139])).

cnf(c_0,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_144,plain,
    ( v1_relat_1(k6_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_242,plain,
    ( v1_relat_1(k6_relat_1(X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_144])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_140,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_245,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k5_relat_1(X1,X0),X2) = k9_relat_1(X0,k9_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_143,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(X1_40)
    | k9_relat_1(k5_relat_1(X1_40,X0_40),X0_39) = k9_relat_1(X0_40,k9_relat_1(X1_40,X0_39)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_243,plain,
    ( k9_relat_1(k5_relat_1(X0_40,X1_40),X0_39) = k9_relat_1(X1_40,k9_relat_1(X0_40,X0_39))
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_448,plain,
    ( k9_relat_1(sK0,k9_relat_1(X0_40,X0_39)) = k9_relat_1(k5_relat_1(X0_40,sK0),X0_39)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_245,c_243])).

cnf(c_468,plain,
    ( k9_relat_1(k5_relat_1(k6_relat_1(X0_41),sK0),X0_39) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0_41),X0_39)) ),
    inference(superposition,[status(thm)],[c_242,c_448])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_142,plain,
    ( ~ v1_relat_1(X0_40)
    | k5_relat_1(k6_relat_1(X0_41),X0_40) = k7_relat_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_244,plain,
    ( k5_relat_1(k6_relat_1(X0_41),X0_40) = k7_relat_1(X0_40,X0_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_321,plain,
    ( k5_relat_1(k6_relat_1(X0_41),sK0) = k7_relat_1(sK0,X0_41) ),
    inference(superposition,[status(thm)],[c_245,c_244])).

cnf(c_470,plain,
    ( k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0_41),X0_39)) = k9_relat_1(k7_relat_1(sK0,X0_41),X0_39) ),
    inference(light_normalisation,[status(thm)],[c_468,c_321])).

cnf(c_614,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_293,c_470])).

cnf(c_149,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_277,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK1),sK2) != X0_39
    | k9_relat_1(sK0,sK2) != X0_39
    | k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_286,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK1),sK2) != k9_relat_1(sK0,sK2)
    | k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k9_relat_1(sK0,sK2) != k9_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_5,negated_conjecture,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_141,negated_conjecture,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_147,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_162,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_146,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_161,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_153,plain,
    ( X0_40 != X1_40
    | X0_39 != X1_39
    | k9_relat_1(X0_40,X0_39) = k9_relat_1(X1_40,X1_39) ),
    theory(equality)).

cnf(c_157,plain,
    ( sK0 != sK0
    | k9_relat_1(sK0,sK2) = k9_relat_1(sK0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_614,c_286,c_141,c_162,c_161,c_157])).


%------------------------------------------------------------------------------
