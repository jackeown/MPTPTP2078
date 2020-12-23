%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0762+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 15.73s
% Output     : CNFRefutation 15.73s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 437 expanded)
%              Number of clauses        :   67 ( 130 expanded)
%              Number of leaves         :    9 (  70 expanded)
%              Depth                    :   21
%              Number of atoms          :  487 (2302 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1138,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2251,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1138])).

fof(f3011,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ~ r1_wellord1(X0,k3_relat_1(X0)) )
        & ( r1_wellord1(X0,k3_relat_1(X0))
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2251])).

fof(f4938,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3011])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f3008,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2246])).

fof(f3009,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3008])).

fof(f4931,plain,(
    ! [X0,X1] :
      ( r1_wellord1(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3009])).

fof(f1132,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2245,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1132])).

fof(f3006,plain,(
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
    inference(nnf_transformation,[],[f2245])).

fof(f3007,plain,(
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
    inference(flattening,[],[f3006])).

fof(f4923,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3007])).

fof(f1126,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2239,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1126])).

fof(f2988,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2239])).

fof(f4899,plain,(
    ! [X0] :
      ( r4_relat_2(X0,k3_relat_1(X0))
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2988])).

fof(f4932,plain,(
    ! [X0,X1] :
      ( r2_wellord1(X0,X1)
      | ~ r1_wellord1(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3009])).

fof(f4937,plain,(
    ! [X0] :
      ( r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3011])).

fof(f4925,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3007])).

fof(f4924,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3007])).

fof(f1127,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2240,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1127])).

fof(f2989,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2240])).

fof(f4901,plain,(
    ! [X0] :
      ( r6_relat_2(X0,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2989])).

fof(f4922,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3007])).

fof(f1128,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2241,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1128])).

fof(f2990,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2241])).

fof(f4903,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2990])).

fof(f4921,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3007])).

fof(f1134,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2247,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1134])).

fof(f3010,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2247])).

fof(f4933,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3010])).

fof(f1139,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1140,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( r2_wellord1(X0,k3_relat_1(X0))
        <=> v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f1139])).

fof(f2252,plain,(
    ? [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <~> v2_wellord1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1140])).

fof(f3012,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2252])).

fof(f3013,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f3012])).

fof(f3014,plain,
    ( ? [X0] :
        ( ( ~ v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) )
        & ( v2_wellord1(X0)
          | r2_wellord1(X0,k3_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ( ~ v2_wellord1(sK277)
        | ~ r2_wellord1(sK277,k3_relat_1(sK277)) )
      & ( v2_wellord1(sK277)
        | r2_wellord1(sK277,k3_relat_1(sK277)) )
      & v1_relat_1(sK277) ) ),
    introduced(choice_axiom,[])).

fof(f3015,plain,
    ( ( ~ v2_wellord1(sK277)
      | ~ r2_wellord1(sK277,k3_relat_1(sK277)) )
    & ( v2_wellord1(sK277)
      | r2_wellord1(sK277,k3_relat_1(sK277)) )
    & v1_relat_1(sK277) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK277])],[f3013,f3014])).

fof(f4940,plain,
    ( v2_wellord1(sK277)
    | r2_wellord1(sK277,k3_relat_1(sK277)) ),
    inference(cnf_transformation,[],[f3015])).

fof(f4939,plain,(
    v1_relat_1(sK277) ),
    inference(cnf_transformation,[],[f3015])).

fof(f4941,plain,
    ( ~ v2_wellord1(sK277)
    | ~ r2_wellord1(sK277,k3_relat_1(sK277)) ),
    inference(cnf_transformation,[],[f3015])).

fof(f4934,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3010])).

fof(f4904,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2990])).

fof(f4902,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2989])).

fof(f4900,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2988])).

fof(f4926,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3007])).

fof(f4929,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3009])).

fof(f4930,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3009])).

fof(f4928,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3009])).

fof(f4927,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3009])).

cnf(c_1906,plain,
    ( ~ r1_wellord1(X0,k3_relat_1(X0))
    | v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4938])).

cnf(c_1897,plain,
    ( ~ r2_wellord1(X0,X1)
    | r1_wellord1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4931])).

cnf(c_1893,plain,
    ( ~ v2_wellord1(X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4923])).

cnf(c_1869,plain,
    ( r4_relat_2(X0,k3_relat_1(X0))
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4899])).

cnf(c_20562,plain,
    ( r4_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1893,c_1869])).

cnf(c_1896,plain,
    ( ~ r1_relat_2(X0,X1)
    | r2_wellord1(X0,X1)
    | ~ r1_wellord1(X0,X1)
    | ~ r8_relat_2(X0,X1)
    | ~ r6_relat_2(X0,X1)
    | ~ r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4932])).

cnf(c_21370,plain,
    ( ~ r1_relat_2(X0,X1)
    | r2_wellord1(X0,X1)
    | ~ r1_wellord1(X0,X1)
    | ~ r8_relat_2(X0,X1)
    | ~ r6_relat_2(X0,X1)
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | X0 != X2
    | k3_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20562,c_1896])).

cnf(c_21371,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | r2_wellord1(X0,k3_relat_1(X0))
    | ~ r1_wellord1(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_21370])).

cnf(c_1907,plain,
    ( r1_wellord1(X0,k3_relat_1(X0))
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4937])).

cnf(c_1891,plain,
    ( ~ v2_wellord1(X0)
    | v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4925])).

cnf(c_1892,plain,
    ( ~ v2_wellord1(X0)
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4924])).

cnf(c_1871,plain,
    ( r6_relat_2(X0,k3_relat_1(X0))
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4901])).

cnf(c_20616,plain,
    ( r6_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1892,c_1871])).

cnf(c_1894,plain,
    ( ~ v2_wellord1(X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4922])).

cnf(c_1873,plain,
    ( r8_relat_2(X0,k3_relat_1(X0))
    | ~ v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4903])).

cnf(c_20670,plain,
    ( r8_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1894,c_1873])).

cnf(c_1895,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4921])).

cnf(c_1903,plain,
    ( r1_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4933])).

cnf(c_20751,plain,
    ( r1_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1895,c_1903])).

cnf(c_21375,plain,
    ( r2_wellord1(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21371,c_1907,c_1891,c_20616,c_20670,c_20751])).

cnf(c_21443,plain,
    ( r1_wellord1(X0,X1)
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k3_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1897,c_21375])).

cnf(c_21444,plain,
    ( r1_wellord1(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_21443])).

cnf(c_1909,negated_conjecture,
    ( r2_wellord1(sK277,k3_relat_1(sK277))
    | v2_wellord1(sK277) ),
    inference(cnf_transformation,[],[f4940])).

cnf(c_13158,plain,
    ( v2_wellord1(sK277)
    | r2_wellord1(sK277,k3_relat_1(sK277)) ),
    inference(prop_impl,[status(thm)],[c_1909])).

cnf(c_13159,plain,
    ( r2_wellord1(sK277,k3_relat_1(sK277))
    | v2_wellord1(sK277) ),
    inference(renaming,[status(thm)],[c_13158])).

cnf(c_21429,plain,
    ( r1_wellord1(X0,X1)
    | v2_wellord1(sK277)
    | ~ v1_relat_1(X0)
    | k3_relat_1(sK277) != X1
    | sK277 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1897,c_13159])).

cnf(c_21430,plain,
    ( r1_wellord1(sK277,k3_relat_1(sK277))
    | v2_wellord1(sK277)
    | ~ v1_relat_1(sK277) ),
    inference(unflattening,[status(thm)],[c_21429])).

cnf(c_1910,negated_conjecture,
    ( v1_relat_1(sK277) ),
    inference(cnf_transformation,[],[f4939])).

cnf(c_21432,plain,
    ( v2_wellord1(sK277)
    | r1_wellord1(sK277,k3_relat_1(sK277)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21430,c_1910])).

cnf(c_21433,plain,
    ( r1_wellord1(sK277,k3_relat_1(sK277))
    | v2_wellord1(sK277) ),
    inference(renaming,[status(thm)],[c_21432])).

cnf(c_21513,plain,
    ( r1_wellord1(X0,k3_relat_1(X0))
    | r1_wellord1(sK277,k3_relat_1(sK277))
    | ~ v1_relat_1(X0)
    | sK277 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21444,c_21433])).

cnf(c_21514,plain,
    ( r1_wellord1(sK277,k3_relat_1(sK277))
    | ~ v1_relat_1(sK277) ),
    inference(unflattening,[status(thm)],[c_21513])).

cnf(c_21516,plain,
    ( r1_wellord1(sK277,k3_relat_1(sK277)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21514,c_1910])).

cnf(c_22979,plain,
    ( v1_wellord1(X0)
    | ~ v1_relat_1(X0)
    | k3_relat_1(X0) != k3_relat_1(sK277)
    | sK277 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1906,c_21516])).

cnf(c_22980,plain,
    ( v1_wellord1(sK277)
    | ~ v1_relat_1(sK277)
    | k3_relat_1(sK277) != k3_relat_1(sK277) ),
    inference(unflattening,[status(thm)],[c_22979])).

cnf(c_1911,plain,
    ( v1_relat_1(sK277) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1910])).

cnf(c_1908,negated_conjecture,
    ( ~ r2_wellord1(sK277,k3_relat_1(sK277))
    | ~ v2_wellord1(sK277) ),
    inference(cnf_transformation,[],[f4941])).

cnf(c_13156,plain,
    ( ~ v2_wellord1(sK277)
    | ~ r2_wellord1(sK277,k3_relat_1(sK277)) ),
    inference(prop_impl,[status(thm)],[c_1908])).

cnf(c_13157,plain,
    ( ~ r2_wellord1(sK277,k3_relat_1(sK277))
    | ~ v2_wellord1(sK277) ),
    inference(renaming,[status(thm)],[c_13156])).

cnf(c_21475,plain,
    ( ~ v2_wellord1(X0)
    | ~ v2_wellord1(sK277)
    | ~ v1_relat_1(X0)
    | k3_relat_1(X0) != k3_relat_1(sK277)
    | sK277 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13157,c_21375])).

cnf(c_21476,plain,
    ( ~ v2_wellord1(sK277)
    | ~ v1_relat_1(sK277)
    | k3_relat_1(sK277) != k3_relat_1(sK277) ),
    inference(unflattening,[status(thm)],[c_21475])).

cnf(c_21478,plain,
    ( ~ v2_wellord1(sK277)
    | k3_relat_1(sK277) != k3_relat_1(sK277) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21476,c_1910])).

cnf(c_1902,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4934])).

cnf(c_1872,plain,
    ( ~ r8_relat_2(X0,k3_relat_1(X0))
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4904])).

cnf(c_1870,plain,
    ( ~ r6_relat_2(X0,k3_relat_1(X0))
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4902])).

cnf(c_1868,plain,
    ( ~ r4_relat_2(X0,k3_relat_1(X0))
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4900])).

cnf(c_1890,plain,
    ( ~ v1_relat_2(X0)
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4926])).

cnf(c_20576,plain,
    ( ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1868,c_1890])).

cnf(c_20630,plain,
    ( ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1870,c_20576])).

cnf(c_20684,plain,
    ( ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1872,c_20630])).

cnf(c_20723,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ r4_relat_2(X0,k3_relat_1(X0))
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1902,c_20684])).

cnf(c_1899,plain,
    ( ~ r2_wellord1(X0,X1)
    | r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4929])).

cnf(c_21391,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r2_wellord1(X1,X2)
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 != X0
    | k3_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20723,c_1899])).

cnf(c_21392,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r2_wellord1(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_21391])).

cnf(c_1898,plain,
    ( ~ r2_wellord1(X0,X1)
    | r6_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4930])).

cnf(c_1900,plain,
    ( ~ r2_wellord1(X0,X1)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4928])).

cnf(c_1901,plain,
    ( r1_relat_2(X0,X1)
    | ~ r2_wellord1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4927])).

cnf(c_21410,plain,
    ( ~ r2_wellord1(X0,k3_relat_1(X0))
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21392,c_1898,c_1900,c_1901])).

cnf(c_21458,plain,
    ( v2_wellord1(X0)
    | v2_wellord1(sK277)
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0)
    | k3_relat_1(X0) != k3_relat_1(sK277)
    | sK277 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13159,c_21410])).

cnf(c_21459,plain,
    ( v2_wellord1(sK277)
    | ~ v1_wellord1(sK277)
    | ~ v1_relat_1(sK277)
    | k3_relat_1(sK277) != k3_relat_1(sK277) ),
    inference(unflattening,[status(thm)],[c_21458])).

cnf(c_21461,plain,
    ( ~ v1_wellord1(sK277)
    | v2_wellord1(sK277)
    | k3_relat_1(sK277) != k3_relat_1(sK277) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21459,c_1910])).

cnf(c_21462,plain,
    ( v2_wellord1(sK277)
    | ~ v1_wellord1(sK277)
    | k3_relat_1(sK277) != k3_relat_1(sK277) ),
    inference(renaming,[status(thm)],[c_21461])).

cnf(c_21487,plain,
    ( ~ v1_wellord1(sK277)
    | k3_relat_1(sK277) != k3_relat_1(sK277) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_21478,c_21462])).

cnf(c_21489,plain,
    ( k3_relat_1(sK277) != k3_relat_1(sK277)
    | v1_wellord1(sK277) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21487])).

cnf(c_22981,plain,
    ( k3_relat_1(sK277) != k3_relat_1(sK277)
    | v1_wellord1(sK277) = iProver_top
    | v1_relat_1(sK277) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22980])).

cnf(c_22982,plain,
    ( k3_relat_1(sK277) != k3_relat_1(sK277) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22980,c_1911,c_21489,c_22981])).

cnf(c_34910,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22982])).

%------------------------------------------------------------------------------
