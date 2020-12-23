%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0668+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:24 EST 2020

% Result     : Theorem 4.74s
% Output     : Refutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  263 ( 946 expanded)
%              Number of leaves         :   54 ( 410 expanded)
%              Depth                    :   15
%              Number of atoms          : 1122 (6788 expanded)
%              Number of equality atoms :  138 (1072 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f87,f89,f93,f94,f95,f100,f104,f108,f112,f116,f120,f124,f128,f145,f150,f319,f336,f341,f345,f360,f365,f434,f440,f445,f459,f467,f481,f482,f496,f6932,f6936,f6952,f7002,f7008,f7070,f7165,f7174,f7196,f7197,f7236,f7247,f7257,f7268,f7273,f7278,f7297,f7306,f7308,f7320,f7359])).

fof(f7359,plain,
    ( ~ spl10_401
    | spl10_303
    | ~ spl10_9
    | ~ spl10_389 ),
    inference(avatar_split_clause,[],[f7357,f6942,f106,f6092,f7000])).

fof(f7000,plain,
    ( spl10_401
  <=> r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_401])])).

fof(f6092,plain,
    ( spl10_303
  <=> r2_hidden(sK6(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_303])])).

fof(f106,plain,
    ( spl10_9
  <=> ! [X6] :
        ( r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f6942,plain,
    ( spl10_389
  <=> sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_389])])).

fof(f7357,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl10_9
    | ~ spl10_389 ),
    inference(superposition,[],[f107,f6943])).

fof(f6943,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl10_389 ),
    inference(avatar_component_clause,[],[f6942])).

fof(f107,plain,
    ( ! [X6] :
        ( r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f7320,plain,
    ( spl10_304
    | ~ spl10_387
    | ~ spl10_388 ),
    inference(avatar_split_clause,[],[f7319,f6938,f6934,f6097])).

fof(f6097,plain,
    ( spl10_304
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_304])])).

fof(f6934,plain,
    ( spl10_387
  <=> sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_387])])).

fof(f6938,plain,
    ( spl10_388
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_388])])).

fof(f7319,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | ~ spl10_387
    | ~ spl10_388 ),
    inference(forward_demodulation,[],[f6939,f6935])).

fof(f6935,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1))
    | ~ spl10_387 ),
    inference(avatar_component_clause,[],[f6934])).

fof(f6939,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK1)
    | ~ spl10_388 ),
    inference(avatar_component_clause,[],[f6938])).

fof(f7308,plain,
    ( sK6(sK0,sK2,sK1) != k1_funct_1(sK1,sK5(sK0,sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2)
    | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f7306,plain,
    ( sK6(sK0,sK2,sK1) != k1_funct_1(sK1,sK5(sK0,sK2,sK1))
    | k1_funct_1(sK1,sK5(sK0,sK2,sK1)) != k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f7297,plain,
    ( ~ spl10_12
    | spl10_1
    | spl10_303
    | ~ spl10_14
    | spl10_304 ),
    inference(avatar_split_clause,[],[f7071,f6097,f126,f6092,f70,f118])).

fof(f118,plain,
    ( spl10_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f70,plain,
    ( spl10_1
  <=> sK1 = k8_relat_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f126,plain,
    ( spl10_14
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f7071,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_14
    | spl10_304 ),
    inference(resolution,[],[f7054,f243])).

fof(f243,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1)
        | r2_hidden(sK6(X2,X3,sK1),X2)
        | sK1 = k8_relat_1(X2,X3)
        | ~ v1_relat_1(X3) )
    | ~ spl10_14 ),
    inference(resolution,[],[f53,f127])).

fof(f127,plain,
    ( v1_relat_1(sK1)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK6(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                    & r2_hidden(sK6(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f7054,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | spl10_304 ),
    inference(avatar_component_clause,[],[f6097])).

fof(f7278,plain,
    ( ~ spl10_386
    | spl10_393 ),
    inference(avatar_contradiction_clause,[],[f7276])).

fof(f7276,plain,
    ( $false
    | ~ spl10_386
    | spl10_393 ),
    inference(subsumption_resolution,[],[f7245,f7275])).

fof(f7275,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X0),sK2)
    | spl10_393 ),
    inference(resolution,[],[f6958,f66])).

fof(f66,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f6958,plain,
    ( ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2))
    | spl10_393 ),
    inference(avatar_component_clause,[],[f6957])).

fof(f6957,plain,
    ( spl10_393
  <=> r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_393])])).

fof(f7245,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2)
    | ~ spl10_386 ),
    inference(avatar_component_clause,[],[f6929])).

fof(f6929,plain,
    ( spl10_386
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_386])])).

fof(f7273,plain,
    ( spl10_401
    | ~ spl10_393
    | ~ spl10_8
    | ~ spl10_411 ),
    inference(avatar_split_clause,[],[f7269,f7255,f102,f6957,f7000])).

fof(f102,plain,
    ( spl10_8
  <=> ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK1))
        | ~ r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X6),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f7255,plain,
    ( spl10_411
  <=> r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_411])])).

fof(f7269,plain,
    ( ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2))
    | r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl10_8
    | ~ spl10_411 ),
    inference(resolution,[],[f7256,f103])).

fof(f103,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK2))
        | r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f7256,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2,sK1)),sK0)
    | ~ spl10_411 ),
    inference(avatar_component_clause,[],[f7255])).

fof(f7268,plain,
    ( ~ spl10_400
    | spl10_410 ),
    inference(avatar_contradiction_clause,[],[f7266])).

fof(f7266,plain,
    ( $false
    | ~ spl10_400
    | spl10_410 ),
    inference(subsumption_resolution,[],[f6994,f7264])).

fof(f7264,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X0),k8_relat_1(sK0,sK2))
    | spl10_410 ),
    inference(resolution,[],[f7253,f66])).

fof(f7253,plain,
    ( ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(k8_relat_1(sK0,sK2)))
    | spl10_410 ),
    inference(avatar_component_clause,[],[f7252])).

fof(f7252,plain,
    ( spl10_410
  <=> r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(k8_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_410])])).

fof(f6994,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),k8_relat_1(sK0,sK2))
    | ~ spl10_400 ),
    inference(avatar_component_clause,[],[f6993])).

fof(f6993,plain,
    ( spl10_400
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_400])])).

fof(f7257,plain,
    ( ~ spl10_410
    | spl10_411
    | ~ spl10_12
    | ~ spl10_15
    | ~ spl10_407 ),
    inference(avatar_split_clause,[],[f7250,f7234,f143,f118,f7255,f7252])).

fof(f143,plain,
    ( spl10_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | k1_funct_1(sK2,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f7234,plain,
    ( spl10_407
  <=> r2_hidden(sK9(k8_relat_1(sK0,sK2),sK5(sK0,sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_407])])).

fof(f7250,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2,sK1)),sK0)
    | ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(k8_relat_1(sK0,sK2)))
    | ~ spl10_12
    | ~ spl10_15
    | ~ spl10_407 ),
    inference(superposition,[],[f7235,f792])).

fof(f792,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK2,X2) = sK9(k8_relat_1(X3,sK2),X2)
        | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,sK2))) )
    | ~ spl10_12
    | ~ spl10_15 ),
    inference(resolution,[],[f788,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | k1_funct_1(sK2,X0) = X1 )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f788,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK9(k8_relat_1(X1,sK2),X0)),sK2)
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK2))) )
    | ~ spl10_12 ),
    inference(resolution,[],[f160,f119])).

fof(f119,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK9(k8_relat_1(X1,X2),X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f129,f67])).

fof(f67,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f129,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f49,f64])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f7235,plain,
    ( r2_hidden(sK9(k8_relat_1(sK0,sK2),sK5(sK0,sK2,sK1)),sK0)
    | ~ spl10_407 ),
    inference(avatar_component_clause,[],[f7234])).

fof(f7247,plain,
    ( spl10_1
    | spl10_400
    | spl10_304
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_303 ),
    inference(avatar_split_clause,[],[f7145,f6092,f126,f118,f6097,f6993,f70])).

fof(f7145,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),k8_relat_1(sK0,sK2))
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_303 ),
    inference(resolution,[],[f1768,f6093])).

fof(f6093,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | ~ spl10_303 ),
    inference(avatar_component_clause,[],[f6092])).

fof(f1768,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(sK6(X5,sK2,sK1),X6)
        | r2_hidden(k4_tarski(sK5(X5,sK2,sK1),sK6(X5,sK2,sK1)),sK1)
        | r2_hidden(k4_tarski(sK5(X5,sK2,sK1),sK6(X5,sK2,sK1)),k8_relat_1(X6,sK2))
        | sK1 = k8_relat_1(X5,sK2) )
    | ~ spl10_12
    | ~ spl10_14 ),
    inference(resolution,[],[f473,f833])).

fof(f833,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X0),sK2)
        | r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl10_12 ),
    inference(resolution,[],[f204,f119])).

fof(f204,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f63,f49])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f473,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK5(X0,sK2,sK1),sK6(X0,sK2,sK1)),sK2)
        | sK1 = k8_relat_1(X0,sK2)
        | r2_hidden(k4_tarski(sK5(X0,sK2,sK1),sK6(X0,sK2,sK1)),sK1) )
    | ~ spl10_12
    | ~ spl10_14 ),
    inference(resolution,[],[f275,f119])).

fof(f275,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1)
        | sK1 = k8_relat_1(X2,X3)
        | r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),X3) )
    | ~ spl10_14 ),
    inference(resolution,[],[f54,f127])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7236,plain,
    ( spl10_407
    | ~ spl10_12
    | ~ spl10_400 ),
    inference(avatar_split_clause,[],[f7225,f6993,f118,f7234])).

fof(f7225,plain,
    ( r2_hidden(sK9(k8_relat_1(sK0,sK2),sK5(sK0,sK2,sK1)),sK0)
    | ~ spl10_12
    | ~ spl10_400 ),
    inference(resolution,[],[f6994,f192])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(X0,sK2))
        | r2_hidden(sK9(k8_relat_1(X0,sK2),X1),X0) )
    | ~ spl10_12 ),
    inference(resolution,[],[f189,f66])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X0,sK2)))
        | r2_hidden(sK9(k8_relat_1(X0,sK2),X1),X0) )
    | ~ spl10_12 ),
    inference(resolution,[],[f175,f119])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK9(k8_relat_1(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f174,f67])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X2,X3))
      | r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X2,X3))
      | r2_hidden(X1,X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7197,plain,
    ( spl10_388
    | ~ spl10_16
    | ~ spl10_401 ),
    inference(avatar_split_clause,[],[f7180,f7000,f148,f6938])).

fof(f148,plain,
    ( spl10_16
  <=> ! [X3,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f7180,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK1)
    | ~ spl10_16
    | ~ spl10_401 ),
    inference(resolution,[],[f7166,f156])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) )
    | ~ spl10_16 ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl10_16 ),
    inference(superposition,[],[f67,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = sK9(sK1,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl10_16 ),
    inference(resolution,[],[f149,f67])).

fof(f149,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 )
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f7166,plain,
    ( r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl10_401 ),
    inference(avatar_component_clause,[],[f7000])).

fof(f7196,plain,
    ( spl10_391
    | ~ spl10_7
    | ~ spl10_401 ),
    inference(avatar_split_clause,[],[f7179,f7000,f98,f6950])).

fof(f6950,plain,
    ( spl10_391
  <=> k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_391])])).

fof(f98,plain,
    ( spl10_7
  <=> ! [X5] :
        ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
        | ~ r2_hidden(X5,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f7179,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl10_7
    | ~ spl10_401 ),
    inference(resolution,[],[f7166,f99])).

fof(f99,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK1))
        | k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f7174,plain,
    ( ~ spl10_393
    | spl10_403
    | ~ spl10_15
    | ~ spl10_391 ),
    inference(avatar_split_clause,[],[f7162,f6950,f143,f7172,f6957])).

fof(f7172,plain,
    ( spl10_403
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_403])])).

fof(f7162,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2)
    | ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2))
    | ~ spl10_15
    | ~ spl10_391 ),
    inference(superposition,[],[f154,f6951])).

fof(f6951,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl10_391 ),
    inference(avatar_component_clause,[],[f6950])).

fof(f154,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl10_15 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl10_15 ),
    inference(superposition,[],[f67,f151])).

fof(f151,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) = sK9(sK2,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl10_15 ),
    inference(resolution,[],[f144,f67])).

fof(f7165,plain,
    ( spl10_1
    | spl10_304
    | spl10_387
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_391 ),
    inference(avatar_split_clause,[],[f7158,f6950,f143,f126,f118,f6934,f6097,f70])).

fof(f7158,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1))
    | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_391 ),
    inference(superposition,[],[f1770,f6951])).

fof(f1770,plain,
    ( ! [X8] :
        ( sK6(X8,sK2,sK1) = k1_funct_1(sK2,sK5(X8,sK2,sK1))
        | r2_hidden(k4_tarski(sK5(X8,sK2,sK1),sK6(X8,sK2,sK1)),sK1)
        | sK1 = k8_relat_1(X8,sK2) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_15 ),
    inference(resolution,[],[f473,f144])).

fof(f7070,plain,
    ( spl10_304
    | spl10_1
    | ~ spl10_12
    | ~ spl10_14
    | spl10_386 ),
    inference(avatar_split_clause,[],[f7052,f6929,f126,f118,f70,f6097])).

fof(f7052,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | ~ spl10_12
    | ~ spl10_14
    | spl10_386 ),
    inference(resolution,[],[f6930,f473])).

fof(f6930,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2)
    | spl10_386 ),
    inference(avatar_component_clause,[],[f6929])).

fof(f7008,plain,
    ( ~ spl10_304
    | spl10_401 ),
    inference(avatar_contradiction_clause,[],[f7004])).

fof(f7004,plain,
    ( $false
    | ~ spl10_304
    | spl10_401 ),
    inference(subsumption_resolution,[],[f6098,f7003])).

fof(f7003,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X0),sK1)
    | spl10_401 ),
    inference(resolution,[],[f7001,f66])).

fof(f7001,plain,
    ( ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))
    | spl10_401 ),
    inference(avatar_component_clause,[],[f7000])).

fof(f6098,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | ~ spl10_304 ),
    inference(avatar_component_clause,[],[f6097])).

fof(f7002,plain,
    ( ~ spl10_401
    | ~ spl10_10
    | spl10_393 ),
    inference(avatar_split_clause,[],[f6997,f6957,f110,f7000])).

fof(f110,plain,
    ( spl10_10
  <=> ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f6997,plain,
    ( ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl10_10
    | spl10_393 ),
    inference(resolution,[],[f6958,f111])).

fof(f111,plain,
    ( ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f6952,plain,
    ( spl10_391
    | ~ spl10_7
    | ~ spl10_304 ),
    inference(avatar_split_clause,[],[f6912,f6097,f98,f6950])).

fof(f6912,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl10_7
    | ~ spl10_304 ),
    inference(resolution,[],[f6098,f520])).

fof(f520,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl10_7 ),
    inference(resolution,[],[f99,f66])).

fof(f6936,plain,
    ( spl10_387
    | ~ spl10_16
    | ~ spl10_304 ),
    inference(avatar_split_clause,[],[f6908,f6097,f148,f6934])).

fof(f6908,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1))
    | ~ spl10_16
    | ~ spl10_304 ),
    inference(resolution,[],[f6098,f149])).

fof(f6932,plain,
    ( ~ spl10_12
    | spl10_1
    | ~ spl10_386
    | ~ spl10_303
    | ~ spl10_14
    | ~ spl10_304 ),
    inference(avatar_split_clause,[],[f6907,f6097,f126,f6092,f6929,f70,f118])).

fof(f6907,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_14
    | ~ spl10_304 ),
    inference(resolution,[],[f6098,f370])).

fof(f370,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1)
        | ~ r2_hidden(sK6(X2,X3,sK1),X2)
        | ~ r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),X3)
        | sK1 = k8_relat_1(X2,X3)
        | ~ v1_relat_1(X3) )
    | ~ spl10_14 ),
    inference(resolution,[],[f55,f127])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f496,plain,
    ( spl10_3
    | ~ spl10_27
    | ~ spl10_28 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | spl10_3
    | ~ spl10_27
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f364,f493])).

fof(f493,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4,X0),sK1)
    | spl10_3
    | ~ spl10_27 ),
    inference(resolution,[],[f490,f344])).

fof(f344,plain,
    ( ! [X19,X20] :
        ( r2_hidden(k4_tarski(X19,X20),sK2)
        | ~ r2_hidden(k4_tarski(X19,X20),sK1) )
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl10_27
  <=> ! [X20,X19] :
        ( ~ r2_hidden(k4_tarski(X19,X20),sK1)
        | r2_hidden(k4_tarski(X19,X20),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f490,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4,X0),sK2)
    | spl10_3 ),
    inference(resolution,[],[f77,f66])).

fof(f77,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK2))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl10_3
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f364,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl10_28
  <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f482,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1)
    | ~ r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f481,plain,
    ( spl10_34
    | ~ spl10_15
    | ~ spl10_27
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f478,f363,f343,f143,f447])).

fof(f447,plain,
    ( spl10_34
  <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f478,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)
    | ~ spl10_15
    | ~ spl10_27
    | ~ spl10_28 ),
    inference(resolution,[],[f364,f350])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK2,X0) = X1 )
    | ~ spl10_15
    | ~ spl10_27 ),
    inference(resolution,[],[f344,f144])).

fof(f467,plain,
    ( ~ spl10_26
    | ~ spl10_28
    | spl10_36 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | ~ spl10_26
    | ~ spl10_28
    | spl10_36 ),
    inference(subsumption_resolution,[],[f364,f464])).

fof(f464,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK4)),sK1)
    | ~ spl10_26
    | spl10_36 ),
    inference(resolution,[],[f458,f339])).

fof(f339,plain,
    ( ! [X15,X16] :
        ( r2_hidden(X16,sK0)
        | ~ r2_hidden(k4_tarski(X15,X16),sK1) )
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl10_26
  <=> ! [X16,X15] :
        ( ~ r2_hidden(k4_tarski(X15,X16),sK1)
        | r2_hidden(X16,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f458,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK4),sK0)
    | spl10_36 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl10_36
  <=> r2_hidden(k1_funct_1(sK1,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f459,plain,
    ( ~ spl10_36
    | spl10_4
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f455,f447,f79,f457])).

fof(f79,plain,
    ( spl10_4
  <=> r2_hidden(k1_funct_1(sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f455,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK4),sK0)
    | spl10_4
    | ~ spl10_34 ),
    inference(forward_demodulation,[],[f80,f448])).

fof(f448,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f447])).

fof(f80,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f445,plain,
    ( spl10_28
    | ~ spl10_16
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f438,f432,f148,f363])).

fof(f432,plain,
    ( spl10_32
  <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f438,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | ~ spl10_16
    | ~ spl10_32 ),
    inference(resolution,[],[f433,f158])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) )
    | ~ spl10_16 ),
    inference(resolution,[],[f156,f66])).

fof(f433,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f432])).

fof(f440,plain,
    ( spl10_2
    | ~ spl10_32 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | spl10_2
    | ~ spl10_32 ),
    inference(resolution,[],[f433,f366])).

fof(f366,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4,X0),sK1)
    | spl10_2 ),
    inference(resolution,[],[f74,f66])).

fof(f74,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK1))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl10_2
  <=> r2_hidden(sK4,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f434,plain,
    ( ~ spl10_3
    | spl10_32
    | ~ spl10_4
    | ~ spl10_15
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f425,f334,f143,f79,f432,f76])).

fof(f334,plain,
    ( spl10_25
  <=> ! [X13,X14] :
        ( ~ r2_hidden(k4_tarski(X13,X14),sK2)
        | r2_hidden(k4_tarski(X13,X14),sK1)
        | ~ r2_hidden(X14,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f425,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl10_4
    | ~ spl10_15
    | ~ spl10_25 ),
    inference(resolution,[],[f400,f86])).

fof(f86,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,X0),sK0)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl10_15
    | ~ spl10_25 ),
    inference(resolution,[],[f335,f154])).

fof(f335,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(k4_tarski(X13,X14),sK2)
        | r2_hidden(k4_tarski(X13,X14),sK1)
        | ~ r2_hidden(X14,sK0) )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f334])).

fof(f365,plain,
    ( spl10_28
    | ~ spl10_2
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f361,f148,f73,f363])).

fof(f361,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | ~ spl10_2
    | ~ spl10_16 ),
    inference(resolution,[],[f85,f156])).

fof(f85,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f360,plain,
    ( spl10_5
    | ~ spl10_15
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f354,f343,f317,f143,f82])).

fof(f82,plain,
    ( spl10_5
  <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f317,plain,
    ( spl10_24
  <=> r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f354,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK1,sK3)
    | ~ spl10_15
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(resolution,[],[f350,f318])).

fof(f318,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f317])).

fof(f345,plain,
    ( ~ spl10_12
    | spl10_27
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f331,f70,f343,f118])).

fof(f331,plain,
    ( ! [X19,X20] :
        ( ~ r2_hidden(k4_tarski(X19,X20),sK1)
        | r2_hidden(k4_tarski(X19,X20),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_1 ),
    inference(superposition,[],[f129,f96])).

fof(f96,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f341,plain,
    ( ~ spl10_12
    | spl10_26
    | ~ spl10_14
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f330,f70,f126,f338,f118])).

fof(f330,plain,
    ( ! [X17,X18] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X17,X18),sK1)
        | r2_hidden(X18,sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_1 ),
    inference(superposition,[],[f65,f96])).

fof(f336,plain,
    ( ~ spl10_12
    | spl10_25
    | ~ spl10_14
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f328,f70,f126,f334,f118])).

fof(f328,plain,
    ( ! [X14,X13] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X13,X14),sK2)
        | ~ r2_hidden(X14,sK0)
        | r2_hidden(k4_tarski(X13,X14),sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_1 ),
    inference(superposition,[],[f63,f96])).

fof(f319,plain,
    ( spl10_24
    | ~ spl10_6
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f315,f148,f91,f317])).

fof(f91,plain,
    ( spl10_6
  <=> r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f315,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1)
    | ~ spl10_6
    | ~ spl10_16 ),
    inference(resolution,[],[f92,f156])).

fof(f92,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f150,plain,
    ( ~ spl10_14
    | spl10_16
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f140,f122,f148,f126])).

fof(f122,plain,
    ( spl10_13
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f140,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3
        | ~ v1_relat_1(sK1) )
    | ~ spl10_13 ),
    inference(resolution,[],[f61,f123])).

fof(f123,plain,
    ( v1_funct_1(sK1)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f145,plain,
    ( ~ spl10_12
    | spl10_15
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f139,f114,f143,f118])).

fof(f114,plain,
    ( spl10_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | k1_funct_1(sK2,X0) = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl10_11 ),
    inference(resolution,[],[f61,f115])).

fof(f115,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f128,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f35,f126])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,k1_relat_1(sK1)) )
      | ( ( ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
          | ~ r2_hidden(sK4,k1_relat_1(sK2))
          | ~ r2_hidden(sK4,k1_relat_1(sK1)) )
        & ( ( r2_hidden(k1_funct_1(sK2,sK4),sK0)
            & r2_hidden(sK4,k1_relat_1(sK2)) )
          | r2_hidden(sK4,k1_relat_1(sK1)) ) )
      | sK1 != k8_relat_1(sK0,sK2) )
    & ( ( ! [X5] :
            ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
            | ~ r2_hidden(X5,k1_relat_1(sK1)) )
        & ! [X6] :
            ( ( r2_hidden(X6,k1_relat_1(sK1))
              | ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
              | ~ r2_hidden(X6,k1_relat_1(sK2)) )
            & ( ( r2_hidden(k1_funct_1(sK2,X6),sK0)
                & r2_hidden(X6,k1_relat_1(sK2)) )
              | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
      | sK1 = k8_relat_1(sK0,sK2) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) )
              | k8_relat_1(X0,X2) != X1 )
            & ( ( ! [X5] :
                    ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) = X1 )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
                & r2_hidden(X3,k1_relat_1(sK1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),sK0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(sK1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),sK0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(sK1)) ) )
            | sK1 != k8_relat_1(sK0,X2) )
          & ( ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(sK1,X5)
                  | ~ r2_hidden(X5,k1_relat_1(sK1)) )
              & ! [X6] :
                  ( ( r2_hidden(X6,k1_relat_1(sK1))
                    | ~ r2_hidden(k1_funct_1(X2,X6),sK0)
                    | ~ r2_hidden(X6,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X6),sK0)
                      & r2_hidden(X6,k1_relat_1(X2)) )
                    | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
            | sK1 = k8_relat_1(sK0,X2) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
              & r2_hidden(X3,k1_relat_1(sK1)) )
          | ? [X4] :
              ( ( ~ r2_hidden(k1_funct_1(X2,X4),sK0)
                | ~ r2_hidden(X4,k1_relat_1(X2))
                | ~ r2_hidden(X4,k1_relat_1(sK1)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),sK0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | r2_hidden(X4,k1_relat_1(sK1)) ) )
          | sK1 != k8_relat_1(sK0,X2) )
        & ( ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(sK1,X5)
                | ~ r2_hidden(X5,k1_relat_1(sK1)) )
            & ! [X6] :
                ( ( r2_hidden(X6,k1_relat_1(sK1))
                  | ~ r2_hidden(k1_funct_1(X2,X6),sK0)
                  | ~ r2_hidden(X6,k1_relat_1(X2)) )
                & ( ( r2_hidden(k1_funct_1(X2,X6),sK0)
                    & r2_hidden(X6,k1_relat_1(X2)) )
                  | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
          | sK1 = k8_relat_1(sK0,X2) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ? [X3] :
            ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
            & r2_hidden(X3,k1_relat_1(sK1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(sK2,X4),sK0)
              | ~ r2_hidden(X4,k1_relat_1(sK2))
              | ~ r2_hidden(X4,k1_relat_1(sK1)) )
            & ( ( r2_hidden(k1_funct_1(sK2,X4),sK0)
                & r2_hidden(X4,k1_relat_1(sK2)) )
              | r2_hidden(X4,k1_relat_1(sK1)) ) )
        | sK1 != k8_relat_1(sK0,sK2) )
      & ( ( ! [X5] :
              ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
              | ~ r2_hidden(X5,k1_relat_1(sK1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(sK1))
                | ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
                | ~ r2_hidden(X6,k1_relat_1(sK2)) )
              & ( ( r2_hidden(k1_funct_1(sK2,X6),sK0)
                  & r2_hidden(X6,k1_relat_1(sK2)) )
                | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
        | sK1 = k8_relat_1(sK0,sK2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
        & r2_hidden(X3,k1_relat_1(sK1)) )
   => ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,k1_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X4] :
        ( ( ~ r2_hidden(k1_funct_1(sK2,X4),sK0)
          | ~ r2_hidden(X4,k1_relat_1(sK2))
          | ~ r2_hidden(X4,k1_relat_1(sK1)) )
        & ( ( r2_hidden(k1_funct_1(sK2,X4),sK0)
            & r2_hidden(X4,k1_relat_1(sK2)) )
          | r2_hidden(X4,k1_relat_1(sK1)) ) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(sK4,k1_relat_1(sK1)) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK4),sK0)
          & r2_hidden(sK4,k1_relat_1(sK2)) )
        | r2_hidden(sK4,k1_relat_1(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                  | ~ r2_hidden(X5,k1_relat_1(X1)) )
              & ! [X6] :
                  ( ( r2_hidden(X6,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                    | ~ r2_hidden(X6,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                      & r2_hidden(X6,k1_relat_1(X2)) )
                    | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <~> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <~> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( k8_relat_1(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
                & ! [X4] :
                    ( r2_hidden(X4,k1_relat_1(X1))
                  <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( k8_relat_1(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
                & ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                  <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                      & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(f124,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f36,f122])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f120,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f37,f118])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f116,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f38,f114])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f112,plain,
    ( spl10_1
    | spl10_10 ),
    inference(avatar_split_clause,[],[f39,f110,f70])).

fof(f39,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_relat_1(sK2))
      | ~ r2_hidden(X6,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,
    ( spl10_1
    | spl10_9 ),
    inference(avatar_split_clause,[],[f40,f106,f70])).

fof(f40,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),sK0)
      | ~ r2_hidden(X6,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f104,plain,
    ( spl10_1
    | spl10_8 ),
    inference(avatar_split_clause,[],[f41,f102,f70])).

fof(f41,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_relat_1(sK1))
      | ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
      | ~ r2_hidden(X6,k1_relat_1(sK2))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f100,plain,
    ( spl10_1
    | spl10_7 ),
    inference(avatar_split_clause,[],[f42,f98,f70])).

fof(f42,plain,(
    ! [X5] :
      ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_3
    | spl10_6 ),
    inference(avatar_split_clause,[],[f43,f91,f76,f73,f70])).

fof(f43,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK2))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_4
    | spl10_6 ),
    inference(avatar_split_clause,[],[f44,f91,f79,f73,f70])).

fof(f44,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | spl10_6 ),
    inference(avatar_split_clause,[],[f45,f91,f79,f76,f73,f70])).

fof(f45,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f46,f82,f76,f73,f70])).

fof(f46,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
    | r2_hidden(sK4,k1_relat_1(sK2))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f47,f82,f79,f73,f70])).

fof(f47,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
    | r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f48,f82,f79,f76,f73,f70])).

fof(f48,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
    | ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
