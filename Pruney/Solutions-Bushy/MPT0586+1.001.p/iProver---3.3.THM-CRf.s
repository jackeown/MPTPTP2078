%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0586+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:39 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
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
fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_relat_1(X0)
        & v1_relat_1(X0) )
     => ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1] :
      ( ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v3_relat_1(k7_relat_1(X0,X1))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( v3_relat_1(X1)
          & ~ v3_relat_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( v3_relat_1(X1)
            & ~ v3_relat_1(k7_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( v3_relat_1(X1)
      & ~ v3_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( v3_relat_1(X1)
      & ~ v3_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( v3_relat_1(X1)
        & ~ v3_relat_1(k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( v3_relat_1(sK1)
      & ~ v3_relat_1(k7_relat_1(sK1,sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( v3_relat_1(sK1)
    & ~ v3_relat_1(k7_relat_1(sK1,sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f14,plain,(
    v3_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    ~ v3_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v3_relat_1(X0)
    | v3_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_53,plain,
    ( ~ v1_relat_1(X0_33)
    | ~ v3_relat_1(X0_33)
    | v3_relat_1(k7_relat_1(X0_33,X0_34)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_55,plain,
    ( ~ v1_relat_1(sK1)
    | v3_relat_1(k7_relat_1(sK1,sK0))
    | ~ v3_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_2,negated_conjecture,
    ( v3_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_3,negated_conjecture,
    ( ~ v3_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55,c_2,c_3,c_4])).


%------------------------------------------------------------------------------
