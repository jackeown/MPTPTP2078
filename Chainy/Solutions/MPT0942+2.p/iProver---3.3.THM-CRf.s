%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0942+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 35.42s
% Output     : CNFRefutation 35.42s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  114 ( 126 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1432,axiom,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6607,plain,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1432])).

fof(f1431,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2883,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1431])).

fof(f6606,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2883])).

fof(f1430,axiom,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6605,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1433,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2884,plain,(
    ! [X0] :
      ( v1_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1433])).

fof(f6608,plain,(
    ! [X0] :
      ( v1_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2884])).

fof(f1423,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6595,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1423])).

fof(f1429,axiom,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6604,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1429])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2550,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f3648,plain,(
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
    inference(nnf_transformation,[],[f2550])).

fof(f3649,plain,(
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
    inference(flattening,[],[f3648])).

fof(f5932,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3649])).

fof(f1434,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1435,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v2_wellord1(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f1434])).

fof(f2885,plain,(
    ? [X0] :
      ( ~ v2_wellord1(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1435])).

fof(f4017,plain,
    ( ? [X0] :
        ( ~ v2_wellord1(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v2_wellord1(k1_wellord2(sK469))
      & v3_ordinal1(sK469) ) ),
    introduced(choice_axiom,[])).

fof(f4018,plain,
    ( ~ v2_wellord1(k1_wellord2(sK469))
    & v3_ordinal1(sK469) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK469])],[f2885,f4017])).

fof(f6610,plain,(
    ~ v2_wellord1(k1_wellord2(sK469)) ),
    inference(cnf_transformation,[],[f4018])).

fof(f6609,plain,(
    v3_ordinal1(sK469) ),
    inference(cnf_transformation,[],[f4018])).

cnf(c_2565,plain,
    ( v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6607])).

cnf(c_137037,plain,
    ( v4_relat_2(k1_wellord2(sK469)) ),
    inference(instantiation,[status(thm)],[c_2565])).

cnf(c_2564,plain,
    ( v6_relat_2(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f6606])).

cnf(c_127028,plain,
    ( v6_relat_2(k1_wellord2(sK469))
    | ~ v3_ordinal1(sK469) ),
    inference(instantiation,[status(thm)],[c_2564])).

cnf(c_2563,plain,
    ( v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6605])).

cnf(c_121715,plain,
    ( v8_relat_2(k1_wellord2(sK469)) ),
    inference(instantiation,[status(thm)],[c_2563])).

cnf(c_2566,plain,
    ( v1_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f6608])).

cnf(c_119598,plain,
    ( v1_wellord1(k1_wellord2(sK469))
    | ~ v3_ordinal1(sK469) ),
    inference(instantiation,[status(thm)],[c_2566])).

cnf(c_2553,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6595])).

cnf(c_117901,plain,
    ( v1_relat_1(k1_wellord2(sK469)) ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_2562,plain,
    ( v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6604])).

cnf(c_117867,plain,
    ( v1_relat_2(k1_wellord2(sK469)) ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_1893,plain,
    ( ~ v1_relat_2(X0)
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5932])).

cnf(c_117815,plain,
    ( ~ v1_relat_2(k1_wellord2(sK469))
    | v2_wellord1(k1_wellord2(sK469))
    | ~ v1_wellord1(k1_wellord2(sK469))
    | ~ v8_relat_2(k1_wellord2(sK469))
    | ~ v6_relat_2(k1_wellord2(sK469))
    | ~ v4_relat_2(k1_wellord2(sK469))
    | ~ v1_relat_1(k1_wellord2(sK469)) ),
    inference(instantiation,[status(thm)],[c_1893])).

cnf(c_2567,negated_conjecture,
    ( ~ v2_wellord1(k1_wellord2(sK469)) ),
    inference(cnf_transformation,[],[f6610])).

cnf(c_2568,negated_conjecture,
    ( v3_ordinal1(sK469) ),
    inference(cnf_transformation,[],[f6609])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_137037,c_127028,c_121715,c_119598,c_117901,c_117867,c_117815,c_2567,c_2568])).

%------------------------------------------------------------------------------
