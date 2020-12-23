%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:15 EST 2020

% Result     : Theorem 3.29s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 255 expanded)
%              Number of leaves         :   29 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  602 (1360 expanded)
%              Number of equality atoms :   79 ( 227 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f106,f136,f148,f162,f935,f1149,f1179])).

fof(f1179,plain,
    ( spl13_1
    | ~ spl13_14
    | ~ spl13_104 ),
    inference(avatar_split_clause,[],[f1177,f1147,f160,f84])).

fof(f84,plain,
    ( spl13_1
  <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f160,plain,
    ( spl13_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f1147,plain,
    ( spl13_104
  <=> ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).

fof(f1177,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | ~ spl13_14
    | ~ spl13_104 ),
    inference(duplicate_literal_removal,[],[f1176])).

fof(f1176,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | ~ spl13_14
    | ~ spl13_104 ),
    inference(resolution,[],[f1162,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f17,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1162,plain,
    ( ! [X4] :
        ( r2_hidden(sK9(k2_relat_1(sK1),X4),k1_relat_1(sK0))
        | r1_tarski(k2_relat_1(sK1),X4) )
    | ~ spl13_14
    | ~ spl13_104 ),
    inference(resolution,[],[f1153,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1153,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl13_14
    | ~ spl13_104 ),
    inference(duplicate_literal_removal,[],[f1150])).

fof(f1150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl13_14
    | ~ spl13_104 ),
    inference(resolution,[],[f1148,f164])).

fof(f164,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK1,X1),k1_relat_1(sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl13_14 ),
    inference(resolution,[],[f161,f80])).

fof(f80,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f38,f41,f40,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f161,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1148,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK1,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl13_104 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f1149,plain,
    ( ~ spl13_4
    | ~ spl13_3
    | spl13_104
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_89 ),
    inference(avatar_split_clause,[],[f1145,f933,f104,f96,f88,f1147,f92,f96])).

fof(f92,plain,
    ( spl13_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f88,plain,
    ( spl13_2
  <=> k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f96,plain,
    ( spl13_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f104,plain,
    ( spl13_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f933,plain,
    ( spl13_89
  <=> ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK1))
        | k1_funct_1(sK1,X5) = sK5(sK1,sK0,X5,sK12(k5_relat_1(sK1,sK0),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_89])])).

fof(f1145,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(sK8(sK1,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_89 ),
    inference(superposition,[],[f1138,f78])).

fof(f78,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK8(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK8(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK6(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK6(X0,X1),X1) )
              & ( ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
                  & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK6(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK8(X0,X5)) = X5
                    & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK6(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK6(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK6(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X5)) = X5
        & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1138,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_89 ),
    inference(duplicate_literal_removal,[],[f1137])).

fof(f1137,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_89 ),
    inference(superposition,[],[f1128,f934])).

fof(f934,plain,
    ( ! [X5] :
        ( k1_funct_1(sK1,X5) = sK5(sK1,sK0,X5,sK12(k5_relat_1(sK1,sK0),X5))
        | ~ r2_hidden(X5,k1_relat_1(sK1)) )
    | ~ spl13_89 ),
    inference(avatar_component_clause,[],[f933])).

fof(f1128,plain,
    ( ! [X6] :
        ( r2_hidden(sK5(sK1,sK0,X6,sK12(k5_relat_1(sK1,sK0),X6)),k1_relat_1(sK0))
        | ~ r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f1100,f80])).

fof(f1100,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK5(sK1,sK0,X0,sK12(k5_relat_1(sK1,sK0),X0)),sK12(k5_relat_1(sK1,sK0),X0)),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f1097,f89])).

fof(f89,plain,
    ( k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1097,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK5(sK1,sK0,X0,sK12(k5_relat_1(sK1,sK0),X0)),sK12(k5_relat_1(sK1,sK0),X0)),sK0)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK0))) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f962,f97])).

fof(f97,plain,
    ( v1_relat_1(sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f962,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK5(X2,sK0,X3,sK12(k5_relat_1(X2,sK0),X3)),sK12(k5_relat_1(X2,sK0),X3)),sK0)
        | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,sK0))) )
    | ~ spl13_6 ),
    inference(resolution,[],[f180,f105])).

fof(f105,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2,sK12(k5_relat_1(X0,X1),X2)),sK12(k5_relat_1(X0,X1),X2)),X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f108,f81])).

fof(f81,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f74,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f74,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f935,plain,
    ( ~ spl13_4
    | ~ spl13_3
    | spl13_89
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f924,f104,f96,f88,f933,f92,f96])).

fof(f924,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK1))
        | k1_funct_1(sK1,X5) = sK5(sK1,sK0,X5,sK12(k5_relat_1(sK1,sK0),X5))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f913,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f913,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK5(sK1,sK0,X0,sK12(k5_relat_1(sK1,sK0),X0))),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f910,f89])).

fof(f910,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK5(sK1,sK0,X0,sK12(k5_relat_1(sK1,sK0),X0))),sK1)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK0))) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f891,f97])).

fof(f891,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(X2,sK5(X3,sK0,X2,sK12(k5_relat_1(X3,sK0),X2))),X3)
        | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK0))) )
    | ~ spl13_6 ),
    inference(resolution,[],[f179,f105])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK5(X1,X2,X0,sK12(k5_relat_1(X1,X2),X0))),X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f107,f81])).

fof(f107,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f75,f63])).

fof(f75,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f162,plain,
    ( ~ spl13_4
    | ~ spl13_3
    | spl13_14
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f158,f146,f160,f92,f96])).

fof(f146,plain,
    ( spl13_12
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl13_12 ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl13_12 ),
    inference(resolution,[],[f147,f79])).

fof(f79,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK8(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK8(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK1,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1) )
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( ~ spl13_4
    | ~ spl13_3
    | spl13_12
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f143,f134,f146,f92,f96])).

fof(f134,plain,
    ( spl13_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f143,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1)
        | ~ r2_hidden(sK8(sK1,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl13_10 ),
    inference(superposition,[],[f135,f78])).

fof(f135,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( ~ spl13_4
    | spl13_10
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f131,f92,f134,f96])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl13_3 ),
    inference(resolution,[],[f82,f93])).

fof(f93,plain,
    ( v1_funct_1(sK1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f45,f104])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
            & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK0))
          & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK0))
        & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
      & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
             => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f98,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f50,f84])).

fof(f50,plain,(
    ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (13912)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (13903)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13912)Refutation not found, incomplete strategy% (13912)------------------------------
% 0.21/0.53  % (13912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13912)Memory used [KB]: 10746
% 0.21/0.53  % (13912)Time elapsed: 0.011 s
% 0.21/0.53  % (13912)------------------------------
% 0.21/0.53  % (13912)------------------------------
% 0.21/0.55  % (13894)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (13919)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (13910)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (13893)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.59  % (13892)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.53/0.59  % (13890)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.59  % (13897)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.60  % (13890)Refutation not found, incomplete strategy% (13890)------------------------------
% 1.53/0.60  % (13890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (13890)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (13890)Memory used [KB]: 10746
% 1.53/0.60  % (13890)Time elapsed: 0.168 s
% 1.53/0.60  % (13890)------------------------------
% 1.53/0.60  % (13890)------------------------------
% 1.53/0.60  % (13920)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.88/0.61  % (13888)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.88/0.62  % (13917)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.88/0.62  % (13906)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.88/0.62  % (13898)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.88/0.62  % (13907)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.88/0.63  % (13916)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.88/0.63  % (13891)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.88/0.63  % (13911)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.88/0.63  % (13913)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.88/0.63  % (13901)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.88/0.63  % (13899)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.88/0.64  % (13902)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.88/0.64  % (13904)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.88/0.64  % (13889)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.88/0.66  % (13905)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.88/0.66  % (13918)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.88/0.66  % (13914)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.88/0.66  % (13994)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.88/0.67  % (13908)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.88/0.67  % (13896)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.88/0.67  % (13900)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 3.15/0.80  % (13995)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.29/0.80  % (13908)Refutation found. Thanks to Tanya!
% 3.29/0.80  % SZS status Theorem for theBenchmark
% 3.29/0.80  % SZS output start Proof for theBenchmark
% 3.29/0.80  fof(f1180,plain,(
% 3.29/0.80    $false),
% 3.29/0.80    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f106,f136,f148,f162,f935,f1149,f1179])).
% 3.29/0.80  fof(f1179,plain,(
% 3.29/0.80    spl13_1 | ~spl13_14 | ~spl13_104),
% 3.29/0.80    inference(avatar_split_clause,[],[f1177,f1147,f160,f84])).
% 3.29/0.80  fof(f84,plain,(
% 3.29/0.80    spl13_1 <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 3.29/0.80  fof(f160,plain,(
% 3.29/0.80    spl13_14 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1))),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 3.29/0.80  fof(f1147,plain,(
% 3.29/0.80    spl13_104 <=> ! [X0] : (r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)))),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).
% 3.29/0.80  fof(f1177,plain,(
% 3.29/0.80    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | (~spl13_14 | ~spl13_104)),
% 3.29/0.80    inference(duplicate_literal_removal,[],[f1176])).
% 3.29/0.80  fof(f1176,plain,(
% 3.29/0.80    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | (~spl13_14 | ~spl13_104)),
% 3.29/0.80    inference(resolution,[],[f1162,f65])).
% 3.29/0.80  fof(f65,plain,(
% 3.29/0.80    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f36])).
% 3.29/0.80  fof(f36,plain,(
% 3.29/0.80    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 3.29/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f17,f35])).
% 3.29/0.80  fof(f35,plain,(
% 3.29/0.80    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f17,plain,(
% 3.29/0.80    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.29/0.80    inference(ennf_transformation,[],[f9])).
% 3.29/0.80  fof(f9,plain,(
% 3.29/0.80    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.29/0.80    inference(unused_predicate_definition_removal,[],[f1])).
% 3.29/0.80  fof(f1,axiom,(
% 3.29/0.80    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.29/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.29/0.80  fof(f1162,plain,(
% 3.29/0.80    ( ! [X4] : (r2_hidden(sK9(k2_relat_1(sK1),X4),k1_relat_1(sK0)) | r1_tarski(k2_relat_1(sK1),X4)) ) | (~spl13_14 | ~spl13_104)),
% 3.29/0.80    inference(resolution,[],[f1153,f64])).
% 3.29/0.80  fof(f64,plain,(
% 3.29/0.80    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f36])).
% 3.29/0.80  fof(f1153,plain,(
% 3.29/0.80    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(X0,k1_relat_1(sK0))) ) | (~spl13_14 | ~spl13_104)),
% 3.29/0.80    inference(duplicate_literal_removal,[],[f1150])).
% 3.29/0.80  fof(f1150,plain,(
% 3.29/0.80    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl13_14 | ~spl13_104)),
% 3.29/0.80    inference(resolution,[],[f1148,f164])).
% 3.29/0.80  fof(f164,plain,(
% 3.29/0.80    ( ! [X1] : (r2_hidden(sK8(sK1,X1),k1_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl13_14),
% 3.29/0.80    inference(resolution,[],[f161,f80])).
% 3.29/0.80  fof(f80,plain,(
% 3.29/0.80    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 3.29/0.80    inference(equality_resolution,[],[f67])).
% 3.29/0.80  fof(f67,plain,(
% 3.29/0.80    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 3.29/0.80    inference(cnf_transformation,[],[f42])).
% 3.29/0.80  fof(f42,plain,(
% 3.29/0.80    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.29/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f38,f41,f40,f39])).
% 3.29/0.80  fof(f39,plain,(
% 3.29/0.80    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f40,plain,(
% 3.29/0.80    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f41,plain,(
% 3.29/0.80    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f38,plain,(
% 3.29/0.80    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.29/0.80    inference(rectify,[],[f37])).
% 3.29/0.80  fof(f37,plain,(
% 3.29/0.80    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.29/0.80    inference(nnf_transformation,[],[f2])).
% 3.29/0.80  fof(f2,axiom,(
% 3.29/0.80    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.29/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 3.29/0.80  fof(f161,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl13_14),
% 3.29/0.80    inference(avatar_component_clause,[],[f160])).
% 3.29/0.80  fof(f1148,plain,(
% 3.29/0.80    ( ! [X0] : (~r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(X0,k1_relat_1(sK0))) ) | ~spl13_104),
% 3.29/0.80    inference(avatar_component_clause,[],[f1147])).
% 3.29/0.80  fof(f1149,plain,(
% 3.29/0.80    ~spl13_4 | ~spl13_3 | spl13_104 | ~spl13_2 | ~spl13_4 | ~spl13_6 | ~spl13_89),
% 3.29/0.80    inference(avatar_split_clause,[],[f1145,f933,f104,f96,f88,f1147,f92,f96])).
% 3.29/0.80  fof(f92,plain,(
% 3.29/0.80    spl13_3 <=> v1_funct_1(sK1)),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 3.29/0.80  fof(f88,plain,(
% 3.29/0.80    spl13_2 <=> k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 3.29/0.80  fof(f96,plain,(
% 3.29/0.80    spl13_4 <=> v1_relat_1(sK1)),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 3.29/0.80  fof(f104,plain,(
% 3.29/0.80    spl13_6 <=> v1_relat_1(sK0)),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 3.29/0.80  fof(f933,plain,(
% 3.29/0.80    spl13_89 <=> ! [X5] : (~r2_hidden(X5,k1_relat_1(sK1)) | k1_funct_1(sK1,X5) = sK5(sK1,sK0,X5,sK12(k5_relat_1(sK1,sK0),X5)))),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_89])])).
% 3.29/0.80  fof(f1145,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl13_2 | ~spl13_4 | ~spl13_6 | ~spl13_89)),
% 3.29/0.80    inference(superposition,[],[f1138,f78])).
% 3.29/0.80  fof(f78,plain,(
% 3.29/0.80    ( ! [X0,X5] : (k1_funct_1(X0,sK8(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(equality_resolution,[],[f58])).
% 3.29/0.80  fof(f58,plain,(
% 3.29/0.80    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK8(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f34])).
% 3.29/0.80  fof(f34,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & ((sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).
% 3.29/0.80  fof(f31,plain,(
% 3.29/0.80    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1))))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f32,plain,(
% 3.29/0.80    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f33,plain,(
% 3.29/0.80    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f30,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(rectify,[],[f29])).
% 3.29/0.80  fof(f29,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(nnf_transformation,[],[f14])).
% 3.29/0.80  fof(f14,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(flattening,[],[f13])).
% 3.29/0.80  fof(f13,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.29/0.80    inference(ennf_transformation,[],[f5])).
% 3.29/0.80  fof(f5,axiom,(
% 3.29/0.80    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.29/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 3.29/0.80  fof(f1138,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl13_2 | ~spl13_4 | ~spl13_6 | ~spl13_89)),
% 3.29/0.80    inference(duplicate_literal_removal,[],[f1137])).
% 3.29/0.80  fof(f1137,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl13_2 | ~spl13_4 | ~spl13_6 | ~spl13_89)),
% 3.29/0.80    inference(superposition,[],[f1128,f934])).
% 3.29/0.80  fof(f934,plain,(
% 3.29/0.80    ( ! [X5] : (k1_funct_1(sK1,X5) = sK5(sK1,sK0,X5,sK12(k5_relat_1(sK1,sK0),X5)) | ~r2_hidden(X5,k1_relat_1(sK1))) ) | ~spl13_89),
% 3.29/0.80    inference(avatar_component_clause,[],[f933])).
% 3.29/0.80  fof(f1128,plain,(
% 3.29/0.80    ( ! [X6] : (r2_hidden(sK5(sK1,sK0,X6,sK12(k5_relat_1(sK1,sK0),X6)),k1_relat_1(sK0)) | ~r2_hidden(X6,k1_relat_1(sK1))) ) | (~spl13_2 | ~spl13_4 | ~spl13_6)),
% 3.29/0.80    inference(resolution,[],[f1100,f80])).
% 3.29/0.80  fof(f1100,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k4_tarski(sK5(sK1,sK0,X0,sK12(k5_relat_1(sK1,sK0),X0)),sK12(k5_relat_1(sK1,sK0),X0)),sK0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl13_2 | ~spl13_4 | ~spl13_6)),
% 3.29/0.80    inference(forward_demodulation,[],[f1097,f89])).
% 3.29/0.80  fof(f89,plain,(
% 3.29/0.80    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) | ~spl13_2),
% 3.29/0.80    inference(avatar_component_clause,[],[f88])).
% 3.29/0.80  fof(f1097,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k4_tarski(sK5(sK1,sK0,X0,sK12(k5_relat_1(sK1,sK0),X0)),sK12(k5_relat_1(sK1,sK0),X0)),sK0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK0)))) ) | (~spl13_4 | ~spl13_6)),
% 3.29/0.80    inference(resolution,[],[f962,f97])).
% 3.29/0.80  fof(f97,plain,(
% 3.29/0.80    v1_relat_1(sK1) | ~spl13_4),
% 3.29/0.80    inference(avatar_component_clause,[],[f96])).
% 3.29/0.80  fof(f962,plain,(
% 3.29/0.80    ( ! [X2,X3] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X2,sK0,X3,sK12(k5_relat_1(X2,sK0),X3)),sK12(k5_relat_1(X2,sK0),X3)),sK0) | ~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,sK0)))) ) | ~spl13_6),
% 3.29/0.80    inference(resolution,[],[f180,f105])).
% 3.29/0.80  fof(f105,plain,(
% 3.29/0.80    v1_relat_1(sK0) | ~spl13_6),
% 3.29/0.80    inference(avatar_component_clause,[],[f104])).
% 3.29/0.80  fof(f180,plain,(
% 3.29/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(sK5(X0,X1,X2,sK12(k5_relat_1(X0,X1),X2)),sK12(k5_relat_1(X0,X1),X2)),X1) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1)))) )),
% 3.29/0.80    inference(resolution,[],[f108,f81])).
% 3.29/0.80  fof(f81,plain,(
% 3.29/0.80    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.29/0.80    inference(equality_resolution,[],[f66])).
% 3.29/0.80  fof(f66,plain,(
% 3.29/0.80    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.29/0.80    inference(cnf_transformation,[],[f42])).
% 3.29/0.80  fof(f108,plain,(
% 3.29/0.80    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(subsumption_resolution,[],[f74,f63])).
% 3.29/0.80  fof(f63,plain,(
% 3.29/0.80    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f16])).
% 3.29/0.80  fof(f16,plain,(
% 3.29/0.80    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(flattening,[],[f15])).
% 3.29/0.80  fof(f15,plain,(
% 3.29/0.80    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.29/0.80    inference(ennf_transformation,[],[f4])).
% 3.29/0.80  fof(f4,axiom,(
% 3.29/0.80    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.29/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 3.29/0.80  fof(f74,plain,(
% 3.29/0.80    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(equality_resolution,[],[f52])).
% 3.29/0.80  fof(f52,plain,(
% 3.29/0.80    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f28])).
% 3.29/0.80  fof(f28,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 3.29/0.80  fof(f25,plain,(
% 3.29/0.80    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f26,plain,(
% 3.29/0.80    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f27,plain,(
% 3.29/0.80    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f24,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(rectify,[],[f23])).
% 3.29/0.80  fof(f23,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(nnf_transformation,[],[f12])).
% 3.29/0.80  fof(f12,plain,(
% 3.29/0.80    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.29/0.80    inference(ennf_transformation,[],[f3])).
% 3.29/0.80  fof(f3,axiom,(
% 3.29/0.80    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.29/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 3.29/0.80  fof(f935,plain,(
% 3.29/0.80    ~spl13_4 | ~spl13_3 | spl13_89 | ~spl13_2 | ~spl13_4 | ~spl13_6),
% 3.29/0.80    inference(avatar_split_clause,[],[f924,f104,f96,f88,f933,f92,f96])).
% 3.29/0.80  fof(f924,plain,(
% 3.29/0.80    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(sK1)) | k1_funct_1(sK1,X5) = sK5(sK1,sK0,X5,sK12(k5_relat_1(sK1,sK0),X5)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl13_2 | ~spl13_4 | ~spl13_6)),
% 3.29/0.80    inference(resolution,[],[f913,f71])).
% 3.29/0.80  fof(f71,plain,(
% 3.29/0.80    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f44])).
% 3.29/0.80  fof(f44,plain,(
% 3.29/0.80    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.29/0.80    inference(flattening,[],[f43])).
% 3.29/0.80  fof(f43,plain,(
% 3.29/0.80    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.29/0.80    inference(nnf_transformation,[],[f19])).
% 3.29/0.80  fof(f19,plain,(
% 3.29/0.80    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.29/0.80    inference(flattening,[],[f18])).
% 3.29/0.80  fof(f18,plain,(
% 3.29/0.80    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.29/0.80    inference(ennf_transformation,[],[f6])).
% 3.29/0.80  fof(f6,axiom,(
% 3.29/0.80    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.29/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 3.29/0.80  fof(f913,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK1,sK0,X0,sK12(k5_relat_1(sK1,sK0),X0))),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl13_2 | ~spl13_4 | ~spl13_6)),
% 3.29/0.80    inference(forward_demodulation,[],[f910,f89])).
% 3.29/0.80  fof(f910,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK1,sK0,X0,sK12(k5_relat_1(sK1,sK0),X0))),sK1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK0)))) ) | (~spl13_4 | ~spl13_6)),
% 3.29/0.80    inference(resolution,[],[f891,f97])).
% 3.29/0.80  fof(f891,plain,(
% 3.29/0.80    ( ! [X2,X3] : (~v1_relat_1(X3) | r2_hidden(k4_tarski(X2,sK5(X3,sK0,X2,sK12(k5_relat_1(X3,sK0),X2))),X3) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK0)))) ) | ~spl13_6),
% 3.29/0.80    inference(resolution,[],[f179,f105])).
% 3.29/0.80  fof(f179,plain,(
% 3.29/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK5(X1,X2,X0,sK12(k5_relat_1(X1,X2),X0))),X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))) )),
% 3.29/0.80    inference(resolution,[],[f107,f81])).
% 3.29/0.80  fof(f107,plain,(
% 3.29/0.80    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(subsumption_resolution,[],[f75,f63])).
% 3.29/0.80  fof(f75,plain,(
% 3.29/0.80    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(equality_resolution,[],[f51])).
% 3.29/0.80  fof(f51,plain,(
% 3.29/0.80    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f28])).
% 3.29/0.80  fof(f162,plain,(
% 3.29/0.80    ~spl13_4 | ~spl13_3 | spl13_14 | ~spl13_12),
% 3.29/0.80    inference(avatar_split_clause,[],[f158,f146,f160,f92,f96])).
% 3.29/0.80  fof(f146,plain,(
% 3.29/0.80    spl13_12 <=> ! [X0] : (r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)))),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 3.29/0.80  fof(f158,plain,(
% 3.29/0.80    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl13_12),
% 3.29/0.80    inference(duplicate_literal_removal,[],[f157])).
% 3.29/0.80  fof(f157,plain,(
% 3.29/0.80    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl13_12),
% 3.29/0.80    inference(resolution,[],[f147,f79])).
% 3.29/0.80  fof(f79,plain,(
% 3.29/0.80    ( ! [X0,X5] : (r2_hidden(sK8(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(equality_resolution,[],[f57])).
% 3.29/0.80  fof(f57,plain,(
% 3.29/0.80    ( ! [X0,X5,X1] : (r2_hidden(sK8(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f34])).
% 3.29/0.80  fof(f147,plain,(
% 3.29/0.80    ( ! [X0] : (~r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1)) ) | ~spl13_12),
% 3.29/0.80    inference(avatar_component_clause,[],[f146])).
% 3.29/0.80  fof(f148,plain,(
% 3.29/0.80    ~spl13_4 | ~spl13_3 | spl13_12 | ~spl13_10),
% 3.29/0.80    inference(avatar_split_clause,[],[f143,f134,f146,f92,f96])).
% 3.29/0.80  fof(f134,plain,(
% 3.29/0.80    spl13_10 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1))),
% 3.29/0.80    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 3.29/0.80  fof(f143,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1) | ~r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl13_10),
% 3.29/0.80    inference(superposition,[],[f135,f78])).
% 3.29/0.80  fof(f135,plain,(
% 3.29/0.80    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl13_10),
% 3.29/0.80    inference(avatar_component_clause,[],[f134])).
% 3.29/0.80  fof(f136,plain,(
% 3.29/0.80    ~spl13_4 | spl13_10 | ~spl13_3),
% 3.29/0.80    inference(avatar_split_clause,[],[f131,f92,f134,f96])).
% 3.29/0.80  fof(f131,plain,(
% 3.29/0.80    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) ) | ~spl13_3),
% 3.29/0.80    inference(resolution,[],[f82,f93])).
% 3.29/0.80  fof(f93,plain,(
% 3.29/0.80    v1_funct_1(sK1) | ~spl13_3),
% 3.29/0.80    inference(avatar_component_clause,[],[f92])).
% 3.29/0.80  fof(f82,plain,(
% 3.29/0.80    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 3.29/0.80    inference(equality_resolution,[],[f72])).
% 3.29/0.80  fof(f72,plain,(
% 3.29/0.80    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.29/0.80    inference(cnf_transformation,[],[f44])).
% 3.29/0.80  fof(f106,plain,(
% 3.29/0.80    spl13_6),
% 3.29/0.80    inference(avatar_split_clause,[],[f45,f104])).
% 3.29/0.80  fof(f45,plain,(
% 3.29/0.80    v1_relat_1(sK0)),
% 3.29/0.80    inference(cnf_transformation,[],[f22])).
% 3.29/0.80  fof(f22,plain,(
% 3.29/0.80    (~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.29/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).
% 3.29/0.80  fof(f20,plain,(
% 3.29/0.80    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f21,plain,(
% 3.29/0.80    ? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.29/0.80    introduced(choice_axiom,[])).
% 3.29/0.80  fof(f11,plain,(
% 3.29/0.80    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.29/0.80    inference(flattening,[],[f10])).
% 3.29/0.80  fof(f10,plain,(
% 3.29/0.80    ? [X0] : (? [X1] : ((~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.29/0.80    inference(ennf_transformation,[],[f8])).
% 3.29/0.80  fof(f8,negated_conjecture,(
% 3.29/0.80    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 3.29/0.80    inference(negated_conjecture,[],[f7])).
% 3.29/0.80  fof(f7,conjecture,(
% 3.29/0.80    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 3.29/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 3.29/0.80  fof(f98,plain,(
% 3.29/0.80    spl13_4),
% 3.29/0.80    inference(avatar_split_clause,[],[f47,f96])).
% 3.29/0.80  fof(f47,plain,(
% 3.29/0.80    v1_relat_1(sK1)),
% 3.29/0.80    inference(cnf_transformation,[],[f22])).
% 3.29/0.80  fof(f94,plain,(
% 3.29/0.80    spl13_3),
% 3.29/0.80    inference(avatar_split_clause,[],[f48,f92])).
% 3.29/0.80  fof(f48,plain,(
% 3.29/0.80    v1_funct_1(sK1)),
% 3.29/0.80    inference(cnf_transformation,[],[f22])).
% 3.29/0.80  fof(f90,plain,(
% 3.29/0.80    spl13_2),
% 3.29/0.80    inference(avatar_split_clause,[],[f49,f88])).
% 3.29/0.80  fof(f49,plain,(
% 3.29/0.80    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)),
% 3.29/0.80    inference(cnf_transformation,[],[f22])).
% 3.29/0.80  fof(f86,plain,(
% 3.29/0.80    ~spl13_1),
% 3.29/0.80    inference(avatar_split_clause,[],[f50,f84])).
% 3.29/0.80  fof(f50,plain,(
% 3.29/0.80    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 3.29/0.80    inference(cnf_transformation,[],[f22])).
% 3.29/0.80  % SZS output end Proof for theBenchmark
% 3.29/0.80  % (13908)------------------------------
% 3.29/0.80  % (13908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.80  % (13908)Termination reason: Refutation
% 3.29/0.80  
% 3.29/0.80  % (13908)Memory used [KB]: 11897
% 3.29/0.80  % (13908)Time elapsed: 0.372 s
% 3.29/0.80  % (13908)------------------------------
% 3.29/0.80  % (13908)------------------------------
% 3.29/0.80  % (13882)Success in time 0.442 s
%------------------------------------------------------------------------------
