%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0605+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Theorem 19.97s
% Output     : CNFRefutation 19.97s
% Verified   : 
% Statistics : Number of formulae       :   25 (  37 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 108 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1331,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f650])).

fof(f1994,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1331])).

fof(f3118,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1994])).

fof(f876,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1589,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f876])).

fof(f1590,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1589])).

fof(f3411,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1590])).

fof(f812,conjecture,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f813,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => k7_relat_1(X1,X0) = X1 ) ),
    inference(negated_conjecture,[],[f812])).

fof(f1513,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f813])).

fof(f1514,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1513])).

fof(f2059,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != X1
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK165,sK164) != sK165
      & v4_relat_1(sK165,sK164)
      & v1_relat_1(sK165) ) ),
    introduced(choice_axiom,[])).

fof(f2060,plain,
    ( k7_relat_1(sK165,sK164) != sK165
    & v4_relat_1(sK165,sK164)
    & v1_relat_1(sK165) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK164,sK165])],[f1514,f2059])).

fof(f3328,plain,(
    k7_relat_1(sK165,sK164) != sK165 ),
    inference(cnf_transformation,[],[f2060])).

fof(f3327,plain,(
    v4_relat_1(sK165,sK164) ),
    inference(cnf_transformation,[],[f2060])).

fof(f3326,plain,(
    v1_relat_1(sK165) ),
    inference(cnf_transformation,[],[f2060])).

cnf(c_1032,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3118])).

cnf(c_59789,plain,
    ( ~ v4_relat_1(sK165,sK164)
    | r1_tarski(k1_relat_1(sK165),sK164)
    | ~ v1_relat_1(sK165) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1324,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f3411])).

cnf(c_55667,plain,
    ( ~ r1_tarski(k1_relat_1(sK165),sK164)
    | ~ v1_relat_1(sK165)
    | k7_relat_1(sK165,sK164) = sK165 ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_1239,negated_conjecture,
    ( k7_relat_1(sK165,sK164) != sK165 ),
    inference(cnf_transformation,[],[f3328])).

cnf(c_1240,negated_conjecture,
    ( v4_relat_1(sK165,sK164) ),
    inference(cnf_transformation,[],[f3327])).

cnf(c_1241,negated_conjecture,
    ( v1_relat_1(sK165) ),
    inference(cnf_transformation,[],[f3326])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59789,c_55667,c_1239,c_1240,c_1241])).

%------------------------------------------------------------------------------
