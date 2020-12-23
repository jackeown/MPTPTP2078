%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1018+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 39.31s
% Output     : CNFRefutation 39.31s
% Verified   : 
% Statistics : Number of formulae       :   46 (  95 expanded)
%              Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 ( 655 expanded)
%              Number of equality atoms :   87 ( 213 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1556,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1557,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f1556])).

fof(f3204,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1557])).

fof(f3205,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f3204])).

fof(f4493,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK545 != sK546
        & k1_funct_1(X1,sK545) = k1_funct_1(X1,sK546)
        & r2_hidden(sK546,X0)
        & r2_hidden(sK545,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4492,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK544,X2) = k1_funct_1(sK544,X3)
          & r2_hidden(X3,sK543)
          & r2_hidden(X2,sK543) )
      & v2_funct_1(sK544)
      & m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
      & v1_funct_2(sK544,sK543,sK543)
      & v1_funct_1(sK544) ) ),
    introduced(choice_axiom,[])).

fof(f4494,plain,
    ( sK545 != sK546
    & k1_funct_1(sK544,sK545) = k1_funct_1(sK544,sK546)
    & r2_hidden(sK546,sK543)
    & r2_hidden(sK545,sK543)
    & v2_funct_1(sK544)
    & m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
    & v1_funct_2(sK544,sK543,sK543)
    & v1_funct_1(sK544) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK543,sK544,sK545,sK546])],[f3205,f4493,f4492])).

fof(f7433,plain,(
    m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) ),
    inference(cnf_transformation,[],[f4494])).

fof(f7437,plain,(
    k1_funct_1(sK544,sK545) = k1_funct_1(sK544,sK546) ),
    inference(cnf_transformation,[],[f4494])).

fof(f1553,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3198,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1553])).

fof(f3199,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f3198])).

fof(f4488,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) ) )
        & ( ! [X2,X3] :
              ( X2 = X3
              | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f3199])).

fof(f4489,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(rectify,[],[f4488])).

fof(f4490,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK541(X0,X1) != sK542(X0,X1)
        & k1_funct_1(X1,sK541(X0,X1)) = k1_funct_1(X1,sK542(X0,X1))
        & r2_hidden(sK542(X0,X1),X0)
        & r2_hidden(sK541(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4491,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ( sK541(X0,X1) != sK542(X0,X1)
            & k1_funct_1(X1,sK541(X0,X1)) = k1_funct_1(X1,sK542(X0,X1))
            & r2_hidden(sK542(X0,X1),X0)
            & r2_hidden(sK541(X0,X1),X0) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK541,sK542])],[f4489,f4490])).

fof(f7421,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f4491])).

fof(f7431,plain,(
    v1_funct_1(sK544) ),
    inference(cnf_transformation,[],[f4494])).

fof(f7434,plain,(
    v2_funct_1(sK544) ),
    inference(cnf_transformation,[],[f4494])).

fof(f7432,plain,(
    v1_funct_2(sK544,sK543,sK543) ),
    inference(cnf_transformation,[],[f4494])).

fof(f7435,plain,(
    r2_hidden(sK545,sK543) ),
    inference(cnf_transformation,[],[f4494])).

fof(f7436,plain,(
    r2_hidden(sK546,sK543) ),
    inference(cnf_transformation,[],[f4494])).

fof(f7438,plain,(
    sK545 != sK546 ),
    inference(cnf_transformation,[],[f4494])).

cnf(c_2917,negated_conjecture,
    ( m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) ),
    inference(cnf_transformation,[],[f7433])).

cnf(c_83929,plain,
    ( m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2917])).

cnf(c_2913,negated_conjecture,
    ( k1_funct_1(sK544,sK545) = k1_funct_1(sK544,sK546) ),
    inference(cnf_transformation,[],[f7437])).

cnf(c_2906,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | X3 = X2
    | k1_funct_1(X0,X3) != k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f7421])).

cnf(c_83935,plain,
    ( X0 = X1
    | k1_funct_1(X2,X0) != k1_funct_1(X2,X1)
    | v1_funct_2(X2,X3,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top
    | r2_hidden(X0,X3) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2906])).

cnf(c_116288,plain,
    ( k1_funct_1(sK544,X0) != k1_funct_1(sK544,sK545)
    | sK546 = X0
    | v1_funct_2(sK544,X1,X1) != iProver_top
    | m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK546,X1) != iProver_top
    | v2_funct_1(sK544) != iProver_top
    | v1_funct_1(sK544) != iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_83935])).

cnf(c_2919,negated_conjecture,
    ( v1_funct_1(sK544) ),
    inference(cnf_transformation,[],[f7431])).

cnf(c_2932,plain,
    ( v1_funct_1(sK544) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2919])).

cnf(c_2916,negated_conjecture,
    ( v2_funct_1(sK544) ),
    inference(cnf_transformation,[],[f7434])).

cnf(c_2935,plain,
    ( v2_funct_1(sK544) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2916])).

cnf(c_116753,plain,
    ( k1_funct_1(sK544,X0) != k1_funct_1(sK544,sK545)
    | sK546 = X0
    | v1_funct_2(sK544,X1,X1) != iProver_top
    | m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK546,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_116288,c_2932,c_2935])).

cnf(c_116764,plain,
    ( sK546 = sK545
    | v1_funct_2(sK544,X0,X0) != iProver_top
    | m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | r2_hidden(sK546,X0) != iProver_top
    | r2_hidden(sK545,X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_116753])).

cnf(c_117193,plain,
    ( sK546 = sK545
    | v1_funct_2(sK544,sK543,sK543) != iProver_top
    | r2_hidden(sK546,sK543) != iProver_top
    | r2_hidden(sK545,sK543) != iProver_top ),
    inference(superposition,[status(thm)],[c_83929,c_116764])).

cnf(c_2918,negated_conjecture,
    ( v1_funct_2(sK544,sK543,sK543) ),
    inference(cnf_transformation,[],[f7432])).

cnf(c_2933,plain,
    ( v1_funct_2(sK544,sK543,sK543) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2918])).

cnf(c_2915,negated_conjecture,
    ( r2_hidden(sK545,sK543) ),
    inference(cnf_transformation,[],[f7435])).

cnf(c_2936,plain,
    ( r2_hidden(sK545,sK543) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2915])).

cnf(c_2914,negated_conjecture,
    ( r2_hidden(sK546,sK543) ),
    inference(cnf_transformation,[],[f7436])).

cnf(c_2937,plain,
    ( r2_hidden(sK546,sK543) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_117231,plain,
    ( sK546 = sK545 ),
    inference(global_propositional_subsumption,[status(thm)],[c_117193,c_2933,c_2936,c_2937])).

cnf(c_2912,negated_conjecture,
    ( sK545 != sK546 ),
    inference(cnf_transformation,[],[f7438])).

cnf(c_117237,plain,
    ( sK545 != sK545 ),
    inference(demodulation,[status(thm)],[c_117231,c_2912])).

cnf(c_117238,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_117237])).

%------------------------------------------------------------------------------
