%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0421+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:15 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   37 (  62 expanded)
%              Number of clauses        :   23 (  24 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :   82 ( 192 expanded)
%              Number of equality atoms :   57 ( 115 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f5])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( sK2 != X1
        & k7_setfam_1(X0,sK2) = k7_setfam_1(X0,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( sK1 != sK2
    & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8,f7])).

fof(f11,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_47,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_48,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,sK1)) = sK1
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_47])).

cnf(c_64,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(X0_35)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | k7_setfam_1(X0_35,k7_setfam_1(X0_35,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_105,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
    inference(equality_resolution,[status(thm)],[c_64])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_38,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_39,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,sK2)) = sK2
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_38])).

cnf(c_65,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(X0_35)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | k7_setfam_1(X0_35,k7_setfam_1(X0_35,sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_108,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_65])).

cnf(c_2,negated_conjecture,
    ( k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_66,negated_conjecture,
    ( k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_109,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_108,c_66])).

cnf(c_140,plain,
    ( sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_105,c_109])).

cnf(c_70,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_96,plain,
    ( sK2 != X0_34
    | sK1 != X0_34
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_97,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_1,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_67,negated_conjecture,
    ( sK1 != sK2 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_68,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_76,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_140,c_97,c_67,c_76])).


%------------------------------------------------------------------------------
