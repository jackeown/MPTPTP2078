%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0787+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:39 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 458 expanded)
%              Number of leaves         :   27 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  740 (2793 expanded)
%              Number of equality atoms :   81 ( 220 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f103,f122,f128,f140,f148,f165,f175,f216,f224,f286,f309,f329,f417])).

fof(f417,plain,
    ( ~ spl13_1
    | spl13_2
    | ~ spl13_8
    | spl13_13 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl13_1
    | spl13_2
    | ~ spl13_8
    | spl13_13 ),
    inference(subsumption_resolution,[],[f415,f101])).

fof(f101,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl13_2
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f415,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_1
    | spl13_2
    | ~ spl13_8
    | spl13_13 ),
    inference(subsumption_resolution,[],[f387,f342])).

fof(f342,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl13_13 ),
    inference(resolution,[],[f308,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f91,f52])).

fof(f52,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
                | sK11(X0,X1,X2) = X1
                | ~ r2_hidden(sK11(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
                  & sK11(X0,X1,X2) != X1 )
                | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
          | sK11(X0,X1,X2) = X1
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
            & sK11(X0,X1,X2) != X1 )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f308,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | spl13_13 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl13_13
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f387,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_1
    | spl13_2
    | ~ spl13_8 ),
    inference(superposition,[],[f88,f374])).

fof(f374,plain,
    ( sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_1
    | spl13_2
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f359,f347])).

fof(f347,plain,
    ( ~ r2_hidden(sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | spl13_2 ),
    inference(resolution,[],[f101,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK12(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK12(X0,X1),X1)
          & r2_hidden(sK12(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK12(X0,X1),X1)
        & r2_hidden(sK12(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f359,plain,
    ( sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl13_1
    | spl13_2
    | ~ spl13_8 ),
    inference(resolution,[],[f353,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f90,f52])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f353,plain,
    ( r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ spl13_1
    | spl13_2
    | ~ spl13_8 ),
    inference(resolution,[],[f352,f101])).

fof(f352,plain,
    ( ! [X0] :
        ( r1_tarski(k1_wellord1(sK2,sK0),X0)
        | r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,sK0),X0),sK1),sK2) )
    | ~ spl13_1
    | ~ spl13_8 ),
    inference(resolution,[],[f349,f88])).

fof(f349,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_wellord1(sK2,sK0))
        | r2_hidden(k4_tarski(X1,sK1),sK2) )
    | ~ spl13_1
    | ~ spl13_8 ),
    inference(resolution,[],[f300,f111])).

fof(f300,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK0),sK2)
        | r2_hidden(k4_tarski(X1,sK1),sK2) )
    | ~ spl13_1
    | ~ spl13_8 ),
    inference(resolution,[],[f96,f164])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) )
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl13_8
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f96,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl13_1
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f329,plain,
    ( spl13_2
    | ~ spl13_12 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl13_2
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f327,f322])).

fof(f322,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl13_2
    | ~ spl13_12 ),
    inference(forward_demodulation,[],[f101,f294])).

fof(f294,plain,
    ( sK0 = sK1
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl13_12
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f327,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl13_2
    | ~ spl13_12 ),
    inference(resolution,[],[f324,f88])).

fof(f324,plain,
    ( ~ r2_hidden(sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))
    | spl13_2
    | ~ spl13_12 ),
    inference(resolution,[],[f322,f89])).

fof(f309,plain,
    ( ~ spl13_13
    | spl13_12
    | ~ spl13_1
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f302,f138,f95,f292,f306])).

fof(f138,plain,
    ( spl13_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f302,plain,
    ( sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl13_1
    | ~ spl13_6 ),
    inference(resolution,[],[f96,f139])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f286,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_10 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f284,f54])).

fof(f54,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f284,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_10 ),
    inference(resolution,[],[f259,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2)) )
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl13_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f259,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),sK2)
    | spl13_1
    | ~ spl13_2
    | ~ spl13_10 ),
    inference(backward_demodulation,[],[f97,f257])).

fof(f257,plain,
    ( sK0 = sK1
    | spl13_1
    | ~ spl13_2
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f256,f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f106,f52])).

fof(f106,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl13_2 ),
    inference(resolution,[],[f104,f93])).

fof(f93,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,sK1))
        | ~ r2_hidden(X0,k1_wellord1(sK2,sK0)) )
    | ~ spl13_2 ),
    inference(resolution,[],[f87,f100])).

fof(f100,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f256,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl13_1
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f251,f97])).

fof(f251,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl13_10 ),
    inference(resolution,[],[f237,f55])).

fof(f55,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f237,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(sK0,X6),sK2)
        | sK0 = X6
        | r2_hidden(X6,k1_wellord1(sK2,sK0)) )
    | ~ spl13_10 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ! [X6] :
        ( r2_hidden(k4_tarski(sK0,X6),sK2)
        | ~ r2_hidden(X6,k3_relat_1(sK2))
        | sK0 = X6
        | sK0 = X6
        | r2_hidden(X6,k1_wellord1(sK2,sK0)) )
    | ~ spl13_10 ),
    inference(resolution,[],[f225,f129])).

fof(f225,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK2)
        | r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0 )
    | ~ spl13_10 ),
    inference(resolution,[],[f215,f54])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl13_10
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f97,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f224,plain,(
    spl13_9 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl13_9 ),
    inference(subsumption_resolution,[],[f222,f52])).

fof(f222,plain,
    ( ~ v1_relat_1(sK2)
    | spl13_9 ),
    inference(subsumption_resolution,[],[f219,f53])).

fof(f53,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f219,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl13_9 ),
    inference(resolution,[],[f212,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f212,plain,
    ( ~ v6_relat_2(sK2)
    | spl13_9 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl13_9
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f216,plain,
    ( ~ spl13_9
    | spl13_10 ),
    inference(avatar_split_clause,[],[f208,f214,f210])).

fof(f208,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | ~ v6_relat_2(sK2)
      | r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    inference(resolution,[],[f65,f52])).

fof(f65,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
            & sK6(X0) != sK7(X0)
            & r2_hidden(sK7(X0),k3_relat_1(X0))
            & r2_hidden(sK6(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
        & sK6(X0) != sK7(X0)
        & r2_hidden(sK7(X0),k3_relat_1(X0))
        & r2_hidden(sK6(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f175,plain,(
    spl13_7 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl13_7 ),
    inference(subsumption_resolution,[],[f173,f52])).

fof(f173,plain,
    ( ~ v1_relat_1(sK2)
    | spl13_7 ),
    inference(subsumption_resolution,[],[f169,f53])).

fof(f169,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl13_7 ),
    inference(resolution,[],[f161,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f161,plain,
    ( ~ v8_relat_2(sK2)
    | spl13_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl13_7
  <=> v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f165,plain,
    ( ~ spl13_7
    | spl13_8 ),
    inference(avatar_split_clause,[],[f157,f163,f159])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(k4_tarski(X2,X0),sK2)
      | ~ v8_relat_2(sK2)
      | r2_hidden(k4_tarski(X2,X1),sK2) ) ),
    inference(resolution,[],[f71,f52])).

fof(f71,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X6),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0)
            & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
            & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0)
        & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
        & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

fof(f148,plain,(
    spl13_5 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl13_5 ),
    inference(subsumption_resolution,[],[f146,f52])).

fof(f146,plain,
    ( ~ v1_relat_1(sK2)
    | spl13_5 ),
    inference(subsumption_resolution,[],[f143,f53])).

fof(f143,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl13_5 ),
    inference(resolution,[],[f136,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f136,plain,
    ( ~ v4_relat_2(sK2)
    | spl13_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl13_5
  <=> v4_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f140,plain,
    ( ~ spl13_5
    | spl13_6 ),
    inference(avatar_split_clause,[],[f132,f138,f134])).

% (20819)Refutation not found, incomplete strategy% (20819)------------------------------
% (20819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20819)Termination reason: Refutation not found, incomplete strategy

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(k4_tarski(X1,X0),sK2)
      | ~ v4_relat_2(sK2)
      | X0 = X1 ) ),
    inference(resolution,[],[f61,f52])).

% (20819)Memory used [KB]: 10618
% (20819)Time elapsed: 0.103 s
% (20819)------------------------------
% (20819)------------------------------
fof(f61,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK4(X0) != sK5(X0)
            & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK4(X0) != sK5(X0)
        & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

fof(f128,plain,(
    spl13_3 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl13_3 ),
    inference(subsumption_resolution,[],[f126,f52])).

fof(f126,plain,
    ( ~ v1_relat_1(sK2)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f124,f53])).

fof(f124,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl13_3 ),
    inference(resolution,[],[f118,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,
    ( ~ v1_relat_2(sK2)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl13_3
  <=> v1_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f122,plain,
    ( ~ spl13_3
    | spl13_4 ),
    inference(avatar_split_clause,[],[f114,f120,f116])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK2))
      | ~ v1_relat_2(sK2)
      | r2_hidden(k4_tarski(X0,X0),sK2) ) ),
    inference(resolution,[],[f58,f52])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | r2_hidden(k4_tarski(X2,X2),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK3(X0),sK3(X0)),X0)
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0),sK3(X0)),X0)
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(f103,plain,
    ( spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f56,f99,f95])).

fof(f56,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f57,f99,f95])).

fof(f57,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
