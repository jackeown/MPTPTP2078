%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0748+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   32 (  62 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 232 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2287,f2296])).

fof(f2296,plain,(
    spl11_57 ),
    inference(avatar_contradiction_clause,[],[f2295])).

fof(f2295,plain,
    ( $false
    | spl11_57 ),
    inference(subsumption_resolution,[],[f2290,f1211])).

fof(f1211,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK6(X4),sK5(X5))
      | ~ r2_hidden(sK6(X4),X4) ) ),
    inference(resolution,[],[f1170,f1167])).

fof(f1167,plain,(
    ! [X2,X0] :
      ( v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK5(X0)) ) ),
    inference(cnf_transformation,[],[f1139])).

fof(f1139,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK5(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK5(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1137,f1138])).

fof(f1138,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK5(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK5(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1137,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f1136])).

fof(f1136,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f1073])).

fof(f1073,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(f1170,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK6(X0))
      | ~ r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f1142])).

fof(f1142,plain,(
    ! [X0] :
      ( ( ~ v3_ordinal1(sK6(X0))
        | ~ r2_hidden(sK6(X0),X0) )
      & ( v3_ordinal1(sK6(X0))
        | r2_hidden(sK6(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1140,f1141])).

fof(f1141,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_ordinal1(X1)
            | ~ r2_hidden(X1,X0) )
          & ( v3_ordinal1(X1)
            | r2_hidden(X1,X0) ) )
     => ( ( ~ v3_ordinal1(sK6(X0))
          | ~ r2_hidden(sK6(X0),X0) )
        & ( v3_ordinal1(sK6(X0))
          | r2_hidden(sK6(X0),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1140,plain,(
    ! [X0] :
    ? [X1] :
      ( ( ~ v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) )
      & ( v3_ordinal1(X1)
        | r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f1115])).

fof(f1115,plain,(
    ! [X0] :
    ? [X1] :
      ( r2_hidden(X1,X0)
    <~> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1093])).

fof(f1093,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f2290,plain,
    ( r2_hidden(sK6(sK5(sK0)),sK5(sK0))
    | spl11_57 ),
    inference(resolution,[],[f2286,f1169])).

fof(f1169,plain,(
    ! [X0] :
      ( v3_ordinal1(sK6(X0))
      | r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f1142])).

fof(f2286,plain,
    ( ~ v3_ordinal1(sK6(sK5(sK0)))
    | spl11_57 ),
    inference(avatar_component_clause,[],[f2285])).

fof(f2285,plain,
    ( spl11_57
  <=> v3_ordinal1(sK6(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f2287,plain,(
    ~ spl11_57 ),
    inference(avatar_split_clause,[],[f2281,f2285])).

fof(f2281,plain,(
    ~ v3_ordinal1(sK6(sK5(sK0))) ),
    inference(resolution,[],[f1808,f1150])).

fof(f1150,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f1124])).

fof(f1124,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1103,f1123])).

fof(f1123,plain,
    ( ? [X0] :
      ! [X1] :
        ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
   => ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) ) ),
    introduced(choice_axiom,[])).

fof(f1103,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1095])).

fof(f1095,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( v3_ordinal1(X1)
           => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f1094])).

fof(f1094,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).

fof(f1808,plain,(
    ! [X0] : ~ r2_hidden(sK6(sK5(X0)),X0) ),
    inference(subsumption_resolution,[],[f1807,f1211])).

fof(f1807,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK6(sK5(X0)),X0) ) ),
    inference(factoring,[],[f1241])).

fof(f1241,plain,(
    ! [X15,X16] :
      ( r2_hidden(sK6(X15),sK5(X16))
      | ~ r2_hidden(sK6(X15),X16)
      | r2_hidden(sK6(X15),X15) ) ),
    inference(resolution,[],[f1168,f1169])).

fof(f1168,plain,(
    ! [X2,X0] :
      ( ~ v3_ordinal1(X2)
      | r2_hidden(X2,sK5(X0))
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1139])).
%------------------------------------------------------------------------------
