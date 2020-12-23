%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0616+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 179 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   18
%              Number of atoms          :  177 (1021 expanded)
%              Number of equality atoms :   39 ( 224 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2795,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2794,f1682])).

fof(f1682,plain,(
    v1_relat_1(sK54) ),
    inference(cnf_transformation,[],[f1374])).

fof(f1374,plain,
    ( ( sK53 != k1_funct_1(sK54,sK52)
      | ~ r2_hidden(sK52,k1_relat_1(sK54))
      | ~ r2_hidden(k4_tarski(sK52,sK53),sK54) )
    & ( ( sK53 = k1_funct_1(sK54,sK52)
        & r2_hidden(sK52,k1_relat_1(sK54)) )
      | r2_hidden(k4_tarski(sK52,sK53),sK54) )
    & v1_funct_1(sK54)
    & v1_relat_1(sK54) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK52,sK53,sK54])],[f1372,f1373])).

fof(f1373,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( sK53 != k1_funct_1(sK54,sK52)
        | ~ r2_hidden(sK52,k1_relat_1(sK54))
        | ~ r2_hidden(k4_tarski(sK52,sK53),sK54) )
      & ( ( sK53 = k1_funct_1(sK54,sK52)
          & r2_hidden(sK52,k1_relat_1(sK54)) )
        | r2_hidden(k4_tarski(sK52,sK53),sK54) )
      & v1_funct_1(sK54)
      & v1_relat_1(sK54) ) ),
    introduced(choice_axiom,[])).

fof(f1372,plain,(
    ? [X0,X1,X2] :
      ( ( k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1371])).

fof(f1371,plain,(
    ? [X0,X1,X2] :
      ( ( k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f901])).

fof(f901,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f900])).

fof(f900,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f894])).

fof(f894,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f893])).

fof(f893,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f2794,plain,(
    ~ v1_relat_1(sK54) ),
    inference(subsumption_resolution,[],[f2793,f1683])).

fof(f1683,plain,(
    v1_funct_1(sK54) ),
    inference(cnf_transformation,[],[f1374])).

fof(f2793,plain,
    ( ~ v1_funct_1(sK54)
    | ~ v1_relat_1(sK54) ),
    inference(resolution,[],[f2792,f1691])).

fof(f1691,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1289])).

fof(f1289,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X2,X1,X0)
          & sP0(X0,X2,X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f903,f1288,f1287])).

fof(f1287,plain,(
    ! [X0,X2,X1] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> r2_hidden(k4_tarski(X1,X2),X0) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1288,plain,(
    ! [X2,X1,X0] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> k1_xboole_0 = X2 )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f903,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f902])).

fof(f902,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f2792,plain,(
    ~ sP0(sK54,sK53,sK52) ),
    inference(global_subsumption,[],[f2749,f2744,f2791])).

fof(f2791,plain,
    ( r2_hidden(k4_tarski(sK52,sK53),sK54)
    | ~ sP0(sK54,sK53,sK52) ),
    inference(subsumption_resolution,[],[f2790,f2716])).

fof(f2716,plain,(
    r2_hidden(sK52,k1_relat_1(sK54)) ),
    inference(subsumption_resolution,[],[f2715,f1682])).

fof(f2715,plain,
    ( r2_hidden(sK52,k1_relat_1(sK54))
    | ~ v1_relat_1(sK54) ),
    inference(duplicate_literal_removal,[],[f2709])).

fof(f2709,plain,
    ( r2_hidden(sK52,k1_relat_1(sK54))
    | r2_hidden(sK52,k1_relat_1(sK54))
    | ~ v1_relat_1(sK54) ),
    inference(resolution,[],[f1684,f1703])).

fof(f1703,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f910])).

fof(f910,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f909])).

fof(f909,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f814])).

fof(f814,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f1684,plain,
    ( r2_hidden(k4_tarski(sK52,sK53),sK54)
    | r2_hidden(sK52,k1_relat_1(sK54)) ),
    inference(cnf_transformation,[],[f1374])).

fof(f2790,plain,
    ( r2_hidden(k4_tarski(sK52,sK53),sK54)
    | ~ r2_hidden(sK52,k1_relat_1(sK54))
    | ~ sP0(sK54,sK53,sK52) ),
    inference(duplicate_literal_removal,[],[f2787])).

fof(f2787,plain,
    ( r2_hidden(k4_tarski(sK52,sK53),sK54)
    | ~ r2_hidden(sK52,k1_relat_1(sK54))
    | ~ sP0(sK54,sK53,sK52)
    | ~ sP0(sK54,sK53,sK52) ),
    inference(superposition,[],[f2636,f2744])).

fof(f2636,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,k1_funct_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f1689])).

fof(f1689,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),X0)
      | k1_funct_1(X0,X2) != X1
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1378])).

fof(f1378,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X0,X2) = X1
          | ~ r2_hidden(k4_tarski(X2,X1),X0) )
        & ( r2_hidden(k4_tarski(X2,X1),X0)
          | k1_funct_1(X0,X2) != X1 ) )
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f1377])).

fof(f1377,plain,(
    ! [X0,X2,X1] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        & ( r2_hidden(k4_tarski(X1,X2),X0)
          | k1_funct_1(X0,X1) != X2 ) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f1287])).

fof(f2744,plain,
    ( sK53 = k1_funct_1(sK54,sK52)
    | ~ sP0(sK54,sK53,sK52) ),
    inference(subsumption_resolution,[],[f2741,f2716])).

fof(f2741,plain,
    ( sK53 = k1_funct_1(sK54,sK52)
    | ~ r2_hidden(sK52,k1_relat_1(sK54))
    | ~ sP0(sK54,sK53,sK52) ),
    inference(duplicate_literal_removal,[],[f2737])).

fof(f2737,plain,
    ( sK53 = k1_funct_1(sK54,sK52)
    | sK53 = k1_funct_1(sK54,sK52)
    | ~ r2_hidden(sK52,k1_relat_1(sK54))
    | ~ sP0(sK54,sK53,sK52) ),
    inference(resolution,[],[f1685,f1690])).

fof(f1690,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X1),X0)
      | k1_funct_1(X0,X2) = X1
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1378])).

fof(f1685,plain,
    ( r2_hidden(k4_tarski(sK52,sK53),sK54)
    | sK53 = k1_funct_1(sK54,sK52) ),
    inference(cnf_transformation,[],[f1374])).

fof(f2749,plain,
    ( ~ r2_hidden(k4_tarski(sK52,sK53),sK54)
    | sK53 != k1_funct_1(sK54,sK52) ),
    inference(subsumption_resolution,[],[f1686,f2716])).

fof(f1686,plain,
    ( sK53 != k1_funct_1(sK54,sK52)
    | ~ r2_hidden(sK52,k1_relat_1(sK54))
    | ~ r2_hidden(k4_tarski(sK52,sK53),sK54) ),
    inference(cnf_transformation,[],[f1374])).
%------------------------------------------------------------------------------
