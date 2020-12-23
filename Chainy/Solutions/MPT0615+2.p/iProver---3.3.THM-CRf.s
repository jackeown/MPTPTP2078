%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0615+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 39.38s
% Output     : CNFRefutation 39.38s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 289 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f945,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f946,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f945])).

fof(f2225,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f946])).

fof(f878,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1609,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f878])).

fof(f3446,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1609])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1685,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f1686,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1685])).

fof(f2172,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1686])).

fof(f4059,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2172])).

fof(f788,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1492,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f788])).

fof(f1493,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1492])).

fof(f3331,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1493])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1328,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f3113,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1328])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1980,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f3074,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1980])).

fof(f824,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f825,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f824])).

fof(f1546,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f825])).

fof(f2089,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1546])).

fof(f2090,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f2089])).

fof(f2092,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
     => ( ( ~ r1_tarski(X0,k7_relat_1(sK165,k1_relat_1(X0)))
          | ~ r1_tarski(X0,sK165) )
        & ( r1_tarski(X0,k7_relat_1(sK165,k1_relat_1(X0)))
          | r1_tarski(X0,sK165) )
        & v1_relat_1(sK165) ) ) ),
    introduced(choice_axiom,[])).

fof(f2091,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | ~ r1_tarski(X0,X1) )
            & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | r1_tarski(X0,X1) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(sK164,k7_relat_1(X1,k1_relat_1(sK164)))
            | ~ r1_tarski(sK164,X1) )
          & ( r1_tarski(sK164,k7_relat_1(X1,k1_relat_1(sK164)))
            | r1_tarski(sK164,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK164) ) ),
    introduced(choice_axiom,[])).

fof(f2093,plain,
    ( ( ~ r1_tarski(sK164,k7_relat_1(sK165,k1_relat_1(sK164)))
      | ~ r1_tarski(sK164,sK165) )
    & ( r1_tarski(sK164,k7_relat_1(sK165,k1_relat_1(sK164)))
      | r1_tarski(sK164,sK165) )
    & v1_relat_1(sK165)
    & v1_relat_1(sK164) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK164,sK165])],[f2090,f2092,f2091])).

fof(f3375,plain,
    ( ~ r1_tarski(sK164,k7_relat_1(sK165,k1_relat_1(sK164)))
    | ~ r1_tarski(sK164,sK165) ),
    inference(cnf_transformation,[],[f2093])).

fof(f3374,plain,
    ( r1_tarski(sK164,k7_relat_1(sK165,k1_relat_1(sK164)))
    | r1_tarski(sK164,sK165) ),
    inference(cnf_transformation,[],[f2093])).

fof(f3373,plain,(
    v1_relat_1(sK165) ),
    inference(cnf_transformation,[],[f2093])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f2225])).

cnf(c_58774,plain,
    ( ~ r1_tarski(X0,sK165)
    | ~ r1_tarski(sK164,X0)
    | r1_tarski(sK164,sK165) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_115438,plain,
    ( ~ r1_tarski(k7_relat_1(sK165,X0),sK165)
    | ~ r1_tarski(sK164,k7_relat_1(sK165,X0))
    | r1_tarski(sK164,sK165) ),
    inference(instantiation,[status(thm)],[c_58774])).

cnf(c_159680,plain,
    ( ~ r1_tarski(k7_relat_1(sK165,k1_relat_1(sK164)),sK165)
    | ~ r1_tarski(sK164,k7_relat_1(sK165,k1_relat_1(sK164)))
    | r1_tarski(sK164,sK165) ),
    inference(instantiation,[status(thm)],[c_115438])).

cnf(c_1326,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3446])).

cnf(c_91204,plain,
    ( r1_tarski(k7_relat_1(sK165,k1_relat_1(sK164)),sK165)
    | ~ v1_relat_1(sK165) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4059])).

cnf(c_59606,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_90751,plain,
    ( r1_tarski(k1_relat_1(sK164),k1_relat_1(sK164)) ),
    inference(instantiation,[status(thm)],[c_59606])).

cnf(c_1211,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3331])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3113])).

cnf(c_953,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3074])).

cnf(c_6412,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1211,c_993,c_953])).

cnf(c_6413,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_6412])).

cnf(c_55244,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k7_relat_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6413])).

cnf(c_1252,negated_conjecture,
    ( ~ r1_tarski(sK164,k7_relat_1(sK165,k1_relat_1(sK164)))
    | ~ r1_tarski(sK164,sK165) ),
    inference(cnf_transformation,[],[f3375])).

cnf(c_55318,plain,
    ( r1_tarski(sK164,k7_relat_1(sK165,k1_relat_1(sK164))) != iProver_top
    | r1_tarski(sK164,sK165) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_80222,plain,
    ( r1_tarski(k1_relat_1(sK164),k1_relat_1(sK164)) != iProver_top
    | r1_tarski(sK164,sK165) != iProver_top
    | v1_relat_1(sK165) != iProver_top ),
    inference(superposition,[status(thm)],[c_55244,c_55318])).

cnf(c_80224,plain,
    ( ~ r1_tarski(k1_relat_1(sK164),k1_relat_1(sK164))
    | ~ r1_tarski(sK164,sK165)
    | ~ v1_relat_1(sK165) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_80222])).

cnf(c_1253,negated_conjecture,
    ( r1_tarski(sK164,k7_relat_1(sK165,k1_relat_1(sK164)))
    | r1_tarski(sK164,sK165) ),
    inference(cnf_transformation,[],[f3374])).

cnf(c_1254,negated_conjecture,
    ( v1_relat_1(sK165) ),
    inference(cnf_transformation,[],[f3373])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_159680,c_91204,c_90751,c_80224,c_1253,c_1254])).

%------------------------------------------------------------------------------
