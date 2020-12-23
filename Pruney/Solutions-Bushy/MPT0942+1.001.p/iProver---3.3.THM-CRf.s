%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0942+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:28 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   43 (  55 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 138 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( v1_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v2_wellord1(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v2_wellord1(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,
    ( ? [X0] :
        ( ~ v2_wellord1(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v2_wellord1(k1_wellord2(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ v2_wellord1(k1_wellord2(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f16])).

fof(f30,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ~ v2_wellord1(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_2(X0)
    | ~ v8_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_wellord1(X0)
    | v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,plain,
    ( ~ v3_ordinal1(X0)
    | v1_wellord1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_152,plain,
    ( v1_wellord1(k1_wellord2(sK0)) ),
    inference(resolution,[status(thm)],[c_11,c_13])).

cnf(c_169,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | ~ v1_relat_2(k1_wellord2(sK0))
    | ~ v8_relat_2(k1_wellord2(sK0))
    | ~ v4_relat_2(k1_wellord2(sK0))
    | ~ v6_relat_2(k1_wellord2(sK0))
    | v2_wellord1(k1_wellord2(sK0)) ),
    inference(resolution,[status(thm)],[c_0,c_152])).

cnf(c_6,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_32,plain,
    ( v1_relat_1(k1_wellord2(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_29,plain,
    ( v1_relat_2(k1_wellord2(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_26,plain,
    ( v8_relat_2(k1_wellord2(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ v3_ordinal1(X0)
    | v6_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_23,plain,
    ( ~ v3_ordinal1(sK0)
    | v6_relat_2(k1_wellord2(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_20,plain,
    ( v4_relat_2(k1_wellord2(sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_12,negated_conjecture,
    ( ~ v2_wellord1(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_169,c_32,c_29,c_26,c_23,c_20,c_12,c_13])).


%------------------------------------------------------------------------------
