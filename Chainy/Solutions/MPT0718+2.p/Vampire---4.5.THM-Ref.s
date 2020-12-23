%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0718+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 16.65s
% Output     : Refutation 16.65s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 138 expanded)
%              Number of leaves         :    8 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 ( 918 expanded)
%              Number of equality atoms :   10 ( 109 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26620,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26557,f5021])).

fof(f5021,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_funct_1(sK1,sK5(sK1))) ),
    inference(resolution,[],[f2203,f1359])).

fof(f1359,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1068])).

fof(f1068,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f2203,plain,(
    v1_xboole_0(k1_funct_1(sK1,sK5(sK1))) ),
    inference(subsumption_resolution,[],[f2202,f1320])).

fof(f1320,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1202])).

fof(f1202,plain,
    ( ~ v2_relat_1(sK1)
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v5_funct_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1053,f1201,f1200])).

fof(f1200,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X1) = k1_relat_1(X0)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(sK0)
          & v5_funct_1(sK0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1201,plain,
    ( ? [X1] :
        ( ~ v2_relat_1(X1)
        & k1_relat_1(X1) = k1_relat_1(sK0)
        & v5_funct_1(sK0,X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_relat_1(sK1)
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v5_funct_1(sK0,sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1053,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X0)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1052])).

fof(f1052,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X0)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f995])).

fof(f995,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X1) = k1_relat_1(X0)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f994])).

fof(f994,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X0)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

fof(f2202,plain,
    ( v1_xboole_0(k1_funct_1(sK1,sK5(sK1)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f2039,f1323])).

fof(f1323,plain,(
    ~ v2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1202])).

fof(f2039,plain,
    ( v2_relat_1(sK1)
    | v1_xboole_0(k1_funct_1(sK1,sK5(sK1)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f1319,f1338])).

fof(f1338,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | v1_xboole_0(k1_funct_1(X0,sK5(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1212])).

fof(f1212,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ( v1_xboole_0(k1_funct_1(X0,sK5(X0)))
            & r2_hidden(sK5(X0),k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1210,f1211])).

fof(f1211,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK5(X0)))
        & r2_hidden(sK5(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1210,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1209])).

fof(f1209,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X1))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1059])).

fof(f1059,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1058])).

fof(f1058,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f900])).

fof(f900,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

fof(f1319,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1202])).

fof(f26557,plain,(
    r2_hidden(k1_funct_1(sK0,sK5(sK1)),k1_funct_1(sK1,sK5(sK1))) ),
    inference(resolution,[],[f2668,f2201])).

fof(f2201,plain,(
    r2_hidden(sK5(sK1),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f2200,f1322])).

fof(f1322,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1202])).

fof(f2200,plain,(
    r2_hidden(sK5(sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f2199,f1320])).

fof(f2199,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f2038,f1323])).

fof(f2038,plain,
    ( v2_relat_1(sK1)
    | r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f1319,f1337])).

fof(f1337,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1212])).

fof(f2668,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f2667,f1319])).

fof(f2667,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f2666,f1320])).

fof(f2666,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK0))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f2665,f1317])).

fof(f1317,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1202])).

fof(f2665,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f2664,f1318])).

fof(f1318,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1202])).

fof(f2664,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1321,f1342])).

fof(f1342,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1216])).

fof(f1216,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK6(X0,X1)),k1_funct_1(X0,sK6(X0,X1)))
                & r2_hidden(sK6(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1214,f1215])).

fof(f1215,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK6(X0,X1)),k1_funct_1(X0,sK6(X0,X1)))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1214,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1213])).

fof(f1213,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1064])).

fof(f1064,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1063])).

fof(f1063,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f901])).

fof(f901,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f1321,plain,(
    v5_funct_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f1202])).
%------------------------------------------------------------------------------
