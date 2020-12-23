%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0907+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 38.91s
% Output     : CNFRefutation 38.91s
% Verified   : 
% Statistics : Number of formulae       :   41 (  69 expanded)
%              Number of clauses        :   19 (  27 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 149 expanded)
%              Number of equality atoms :   55 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1374,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1375,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f1374])).

fof(f2767,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1375])).

fof(f3821,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( k2_mcart_1(sK414) = sK414
        | k1_mcart_1(sK414) = sK414 )
      & r2_hidden(sK414,k2_zfmisc_1(sK415,sK416)) ) ),
    introduced(choice_axiom,[])).

fof(f3822,plain,
    ( ( k2_mcart_1(sK414) = sK414
      | k1_mcart_1(sK414) = sK414 )
    & r2_hidden(sK414,k2_zfmisc_1(sK415,sK416)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK414,sK415,sK416])],[f2767,f3821])).

fof(f6257,plain,
    ( k2_mcart_1(sK414) = sK414
    | k1_mcart_1(sK414) = sK414 ),
    inference(cnf_transformation,[],[f3822])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4945,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f6256,plain,(
    r2_hidden(sK414,k2_zfmisc_1(sK415,sK416)) ),
    inference(cnf_transformation,[],[f3822])).

fof(f1328,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2729,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1328])).

fof(f2730,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2729])).

fof(f6153,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2730])).

fof(f1327,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2728,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f1327])).

fof(f6152,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f2728])).

fof(f7391,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f6152])).

fof(f1377,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6261,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1377])).

fof(f6151,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f2728])).

fof(f7392,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f6151])).

fof(f6260,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1377])).

cnf(c_2410,negated_conjecture,
    ( k2_mcart_1(sK414) = sK414
    | k1_mcart_1(sK414) = sK414 ),
    inference(cnf_transformation,[],[f6257])).

cnf(c_1104,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4945])).

cnf(c_69507,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1104])).

cnf(c_2411,negated_conjecture,
    ( r2_hidden(sK414,k2_zfmisc_1(sK415,sK416)) ),
    inference(cnf_transformation,[],[f6256])).

cnf(c_68392,plain,
    ( r2_hidden(sK414,k2_zfmisc_1(sK415,sK416)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_2307,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6153])).

cnf(c_68449,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2307])).

cnf(c_90333,plain,
    ( k4_tarski(k1_mcart_1(sK414),k2_mcart_1(sK414)) = sK414
    | v1_relat_1(k2_zfmisc_1(sK415,sK416)) != iProver_top ),
    inference(superposition,[status(thm)],[c_68392,c_68449])).

cnf(c_113681,plain,
    ( k4_tarski(k1_mcart_1(sK414),k2_mcart_1(sK414)) = sK414 ),
    inference(superposition,[status(thm)],[c_69507,c_90333])).

cnf(c_114335,plain,
    ( k4_tarski(k1_mcart_1(sK414),sK414) = sK414
    | k1_mcart_1(sK414) = sK414 ),
    inference(superposition,[status(thm)],[c_2410,c_113681])).

cnf(c_2305,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7391])).

cnf(c_2414,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6261])).

cnf(c_70611,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_2305,c_2414])).

cnf(c_138410,plain,
    ( k1_mcart_1(sK414) = sK414 ),
    inference(superposition,[status(thm)],[c_114335,c_70611])).

cnf(c_2306,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7392])).

cnf(c_2415,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6260])).

cnf(c_70608,plain,
    ( k4_tarski(X0,X1) != X0 ),
    inference(light_normalisation,[status(thm)],[c_2306,c_2415])).

cnf(c_138380,plain,
    ( k1_mcart_1(sK414) != sK414 ),
    inference(superposition,[status(thm)],[c_113681,c_70608])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_138410,c_138380])).

%------------------------------------------------------------------------------
