%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0783+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:53 EST 2020

% Result     : Theorem 35.17s
% Output     : CNFRefutation 35.17s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 140 expanded)
%              Number of clauses        :   34 (  38 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  250 ( 584 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1159,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2312,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1159])).

fof(f2313,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2312])).

fof(f5098,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2313])).

fof(f1157,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2308,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1157])).

fof(f2309,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2308])).

fof(f5096,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2309])).

fof(f1158,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2310,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1158])).

fof(f2311,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2310])).

fof(f5097,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2311])).

fof(f1166,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
       => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2322,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1166])).

fof(f2323,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2322])).

fof(f5105,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2323])).

fof(f1139,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2283,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1139])).

fof(f5057,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2283])).

fof(f1156,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
       => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2306,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1156])).

fof(f2307,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2306])).

fof(f5095,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2307])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2278,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f3087,plain,(
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
    inference(nnf_transformation,[],[f2278])).

fof(f3088,plain,(
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
    inference(flattening,[],[f3087])).

fof(f5040,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3088])).

fof(f1167,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1168,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1167])).

fof(f2324,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1168])).

fof(f2325,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f2324])).

fof(f3122,plain,
    ( ? [X0,X1] :
        ( ~ v2_wellord1(k2_wellord1(X1,X0))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(k2_wellord1(sK293,sK292))
      & v2_wellord1(sK293)
      & v1_relat_1(sK293) ) ),
    introduced(choice_axiom,[])).

fof(f3123,plain,
    ( ~ v2_wellord1(k2_wellord1(sK293,sK292))
    & v2_wellord1(sK293)
    & v1_relat_1(sK293) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK292,sK293])],[f2325,f3122])).

fof(f5107,plain,(
    v2_wellord1(sK293) ),
    inference(cnf_transformation,[],[f3123])).

fof(f5039,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3088])).

fof(f5038,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3088])).

fof(f5037,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3088])).

fof(f5036,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3088])).

fof(f5041,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3088])).

fof(f5108,plain,(
    ~ v2_wellord1(k2_wellord1(sK293,sK292)) ),
    inference(cnf_transformation,[],[f3123])).

fof(f5106,plain,(
    v1_relat_1(sK293) ),
    inference(cnf_transformation,[],[f3123])).

cnf(c_1955,plain,
    ( ~ v4_relat_2(X0)
    | v4_relat_2(k2_wellord1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5098])).

cnf(c_111925,plain,
    ( v4_relat_2(k2_wellord1(sK293,sK292))
    | ~ v4_relat_2(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_1953,plain,
    ( ~ v6_relat_2(X0)
    | v6_relat_2(k2_wellord1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5096])).

cnf(c_111910,plain,
    ( v6_relat_2(k2_wellord1(sK293,sK292))
    | ~ v6_relat_2(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_1954,plain,
    ( ~ v8_relat_2(X0)
    | v8_relat_2(k2_wellord1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5097])).

cnf(c_104817,plain,
    ( v8_relat_2(k2_wellord1(sK293,sK292))
    | ~ v8_relat_2(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_1962,plain,
    ( ~ v1_wellord1(X0)
    | v1_wellord1(k2_wellord1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5105])).

cnf(c_95999,plain,
    ( v1_wellord1(k2_wellord1(sK293,sK292))
    | ~ v1_wellord1(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_1914,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f5057])).

cnf(c_93367,plain,
    ( v1_relat_1(k2_wellord1(sK293,sK292))
    | ~ v1_relat_1(sK293) ),
    inference(instantiation,[status(thm)],[c_1914])).

cnf(c_1952,plain,
    ( ~ v1_relat_2(X0)
    | v1_relat_2(k2_wellord1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5095])).

cnf(c_93338,plain,
    ( v1_relat_2(k2_wellord1(sK293,sK292))
    | ~ v1_relat_2(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_1894,plain,
    ( ~ v2_wellord1(X0)
    | v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5040])).

cnf(c_1964,negated_conjecture,
    ( v2_wellord1(sK293) ),
    inference(cnf_transformation,[],[f5107])).

cnf(c_32452,plain,
    ( v1_wellord1(X0)
    | ~ v1_relat_1(X0)
    | sK293 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1894,c_1964])).

cnf(c_32453,plain,
    ( v1_wellord1(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(unflattening,[status(thm)],[c_32452])).

cnf(c_1895,plain,
    ( ~ v2_wellord1(X0)
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5039])).

cnf(c_32441,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK293 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1895,c_1964])).

cnf(c_32442,plain,
    ( v6_relat_2(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(unflattening,[status(thm)],[c_32441])).

cnf(c_1896,plain,
    ( ~ v2_wellord1(X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5038])).

cnf(c_32430,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK293 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1896,c_1964])).

cnf(c_32431,plain,
    ( v4_relat_2(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(unflattening,[status(thm)],[c_32430])).

cnf(c_1897,plain,
    ( ~ v2_wellord1(X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5037])).

cnf(c_32419,plain,
    ( v8_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK293 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1897,c_1964])).

cnf(c_32420,plain,
    ( v8_relat_2(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(unflattening,[status(thm)],[c_32419])).

cnf(c_1898,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5036])).

cnf(c_32408,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK293 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1898,c_1964])).

cnf(c_32409,plain,
    ( v1_relat_2(sK293)
    | ~ v1_relat_1(sK293) ),
    inference(unflattening,[status(thm)],[c_32408])).

cnf(c_1893,plain,
    ( ~ v1_relat_2(X0)
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5041])).

cnf(c_1963,negated_conjecture,
    ( ~ v2_wellord1(k2_wellord1(sK293,sK292)) ),
    inference(cnf_transformation,[],[f5108])).

cnf(c_32361,plain,
    ( ~ v1_relat_2(X0)
    | ~ v1_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK293,sK292) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1893,c_1963])).

cnf(c_32362,plain,
    ( ~ v1_relat_2(k2_wellord1(sK293,sK292))
    | ~ v1_wellord1(k2_wellord1(sK293,sK292))
    | ~ v8_relat_2(k2_wellord1(sK293,sK292))
    | ~ v6_relat_2(k2_wellord1(sK293,sK292))
    | ~ v4_relat_2(k2_wellord1(sK293,sK292))
    | ~ v1_relat_1(k2_wellord1(sK293,sK292)) ),
    inference(unflattening,[status(thm)],[c_32361])).

cnf(c_1965,negated_conjecture,
    ( v1_relat_1(sK293) ),
    inference(cnf_transformation,[],[f5106])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_111925,c_111910,c_104817,c_95999,c_93367,c_93338,c_32453,c_32442,c_32431,c_32420,c_32409,c_32362,c_1965])).

%------------------------------------------------------------------------------
