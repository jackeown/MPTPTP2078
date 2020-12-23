%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0753+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   37 (  64 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 326 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6220,f6226,f6232])).

fof(f6232,plain,(
    spl243_1 ),
    inference(avatar_contradiction_clause,[],[f6231])).

fof(f6231,plain,
    ( $false
    | spl243_1 ),
    inference(subsumption_resolution,[],[f6230,f2847])).

fof(f2847,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f2192])).

fof(f2192,plain,
    ( ( ~ v5_ordinal1(sK5)
      | ~ v1_funct_1(sK5)
      | ~ v5_relat_1(sK5,k2_relat_1(sK5))
      | ~ v1_relat_1(sK5) )
    & v3_ordinal1(k1_relat_1(sK5))
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1131,f2191])).

fof(f2191,plain,
    ( ? [X0] :
        ( ( ~ v5_ordinal1(X0)
          | ~ v1_funct_1(X0)
          | ~ v5_relat_1(X0,k2_relat_1(X0))
          | ~ v1_relat_1(X0) )
        & v3_ordinal1(k1_relat_1(X0))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v5_ordinal1(sK5)
        | ~ v1_funct_1(sK5)
        | ~ v5_relat_1(sK5,k2_relat_1(sK5))
        | ~ v1_relat_1(sK5) )
      & v3_ordinal1(k1_relat_1(sK5))
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1131,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1130])).

fof(f1130,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1106])).

fof(f1106,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v3_ordinal1(k1_relat_1(X0))
         => ( v5_ordinal1(X0)
            & v1_funct_1(X0)
            & v5_relat_1(X0,k2_relat_1(X0))
            & v1_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f1105])).

fof(f1105,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_ordinal1(k1_relat_1(X0))
       => ( v5_ordinal1(X0)
          & v1_funct_1(X0)
          & v5_relat_1(X0,k2_relat_1(X0))
          & v1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_ordinal1)).

fof(f6230,plain,
    ( ~ v1_relat_1(sK5)
    | spl243_1 ),
    inference(subsumption_resolution,[],[f6228,f4751])).

fof(f4751,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f3870])).

fof(f3870,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2561])).

fof(f2561,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2560])).

fof(f2560,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6228,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl243_1 ),
    inference(resolution,[],[f3521,f6215])).

fof(f6215,plain,
    ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | spl243_1 ),
    inference(avatar_component_clause,[],[f6213])).

fof(f6213,plain,
    ( spl243_1
  <=> v5_relat_1(sK5,k2_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl243_1])])).

fof(f3521,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2431])).

fof(f2431,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1503])).

fof(f1503,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f6226,plain,(
    spl243_2 ),
    inference(avatar_contradiction_clause,[],[f6225])).

fof(f6225,plain,
    ( $false
    | spl243_2 ),
    inference(subsumption_resolution,[],[f6223,f2849])).

fof(f2849,plain,(
    v3_ordinal1(k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f2192])).

fof(f6223,plain,
    ( ~ v3_ordinal1(k1_relat_1(sK5))
    | spl243_2 ),
    inference(resolution,[],[f3290,f6219])).

fof(f6219,plain,
    ( ~ v5_ordinal1(sK5)
    | spl243_2 ),
    inference(avatar_component_clause,[],[f6217])).

fof(f6217,plain,
    ( spl243_2
  <=> v5_ordinal1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl243_2])])).

fof(f3290,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v3_ordinal1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f2346])).

fof(f2346,plain,(
    ! [X0] :
      ( ( v5_ordinal1(X0)
        | ~ v3_ordinal1(k1_relat_1(X0)) )
      & ( v3_ordinal1(k1_relat_1(X0))
        | ~ v5_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f1064])).

fof(f1064,axiom,(
    ! [X0] :
      ( v5_ordinal1(X0)
    <=> v3_ordinal1(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_ordinal1)).

fof(f6220,plain,
    ( ~ spl243_1
    | ~ spl243_2 ),
    inference(avatar_split_clause,[],[f6211,f6217,f6213])).

fof(f6211,plain,
    ( ~ v5_ordinal1(sK5)
    | ~ v5_relat_1(sK5,k2_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f6210,f2847])).

fof(f6210,plain,
    ( ~ v5_ordinal1(sK5)
    | ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f2850,f2848])).

fof(f2848,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f2192])).

fof(f2850,plain,
    ( ~ v5_ordinal1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f2192])).
%------------------------------------------------------------------------------
