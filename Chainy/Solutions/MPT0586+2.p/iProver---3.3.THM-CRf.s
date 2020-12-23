%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0586+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 18.24s
% Output     : CNFRefutation 18.24s
% Verified   : 
% Statistics : Number of formulae       :   20 (  32 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  94 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f680,axiom,(
    ! [X0,X1] :
      ( ( v3_relat_1(X0)
        & v1_relat_1(X0) )
     => ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1320,plain,(
    ! [X0,X1] :
      ( ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f680])).

fof(f1321,plain,(
    ! [X0,X1] :
      ( ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1320])).

fof(f3088,plain,(
    ! [X0,X1] :
      ( v3_relat_1(k7_relat_1(X0,X1))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1321])).

fof(f779,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( v3_relat_1(X1)
          & ~ v3_relat_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f780,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( v3_relat_1(X1)
            & ~ v3_relat_1(k7_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f779])).

fof(f1439,plain,(
    ? [X0,X1] :
      ( v3_relat_1(X1)
      & ~ v3_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f780])).

fof(f1440,plain,(
    ? [X0,X1] :
      ( v3_relat_1(X1)
      & ~ v3_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1439])).

fof(f1977,plain,
    ( ? [X0,X1] :
        ( v3_relat_1(X1)
        & ~ v3_relat_1(k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( v3_relat_1(sK162)
      & ~ v3_relat_1(k7_relat_1(sK162,sK161))
      & v1_relat_1(sK162) ) ),
    introduced(choice_axiom,[])).

fof(f1978,plain,
    ( v3_relat_1(sK162)
    & ~ v3_relat_1(k7_relat_1(sK162,sK161))
    & v1_relat_1(sK162) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK161,sK162])],[f1440,f1977])).

fof(f3202,plain,(
    v3_relat_1(sK162) ),
    inference(cnf_transformation,[],[f1978])).

fof(f3201,plain,(
    ~ v3_relat_1(k7_relat_1(sK162,sK161)) ),
    inference(cnf_transformation,[],[f1978])).

fof(f3200,plain,(
    v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f1978])).

cnf(c_1080,plain,
    ( ~ v3_relat_1(X0)
    | v3_relat_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3088])).

cnf(c_61873,plain,
    ( v3_relat_1(k7_relat_1(sK162,X0))
    | ~ v3_relat_1(sK162)
    | ~ v1_relat_1(sK162) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_71288,plain,
    ( v3_relat_1(k7_relat_1(sK162,sK161))
    | ~ v3_relat_1(sK162)
    | ~ v1_relat_1(sK162) ),
    inference(instantiation,[status(thm)],[c_61873])).

cnf(c_1193,negated_conjecture,
    ( v3_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3202])).

cnf(c_1194,negated_conjecture,
    ( ~ v3_relat_1(k7_relat_1(sK162,sK161)) ),
    inference(cnf_transformation,[],[f3201])).

cnf(c_1195,negated_conjecture,
    ( v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3200])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71288,c_1193,c_1194,c_1195])).

%------------------------------------------------------------------------------
