%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:15 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 230 expanded)
%              Number of leaves         :   32 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  505 (1021 expanded)
%              Number of equality atoms :   66 ( 137 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f427,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f90,f94,f102,f130,f136,f152,f198,f211,f344,f360,f413,f418])).

fof(f418,plain,
    ( spl13_1
    | ~ spl13_38 ),
    inference(avatar_split_clause,[],[f414,f411,f80])).

fof(f80,plain,
    ( spl13_1
  <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f411,plain,
    ( spl13_38
  <=> r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f414,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | ~ spl13_38 ),
    inference(resolution,[],[f412,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
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

fof(f412,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl13_38 ),
    inference(avatar_component_clause,[],[f411])).

fof(f413,plain,
    ( ~ spl13_13
    | spl13_38
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_33 ),
    inference(avatar_split_clause,[],[f409,f358,f100,f92,f411,f150])).

fof(f150,plain,
    ( spl13_13
  <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f92,plain,
    ( spl13_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f100,plain,
    ( spl13_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f358,plain,
    ( spl13_33
  <=> sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f409,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0))
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_33 ),
    inference(superposition,[],[f384,f359])).

fof(f359,plain,
    ( sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f358])).

fof(f384,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK5(sK1,sK0,X2,X3),k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(sK1,sK0)) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f380,f77])).

fof(f77,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f37,f40,f39,f38])).

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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

fof(f380,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK5(sK1,sK0,X0,X1),X1),sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f378,f93])).

fof(f93,plain,
    ( v1_relat_1(sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f378,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X5)
        | r2_hidden(k4_tarski(sK5(X5,sK0,X3,X4),X4),sK0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X5,sK0)) )
    | ~ spl13_6 ),
    inference(resolution,[],[f104,f101])).

fof(f101,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f104,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f70,f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f70,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f360,plain,
    ( spl13_33
    | ~ spl13_10
    | ~ spl13_21
    | ~ spl13_23
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f356,f342,f209,f196,f134,f358])).

fof(f134,plain,
    ( spl13_10
  <=> r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f196,plain,
    ( spl13_21
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f209,plain,
    ( spl13_23
  <=> sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f342,plain,
    ( spl13_30
  <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f356,plain,
    ( sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))
    | ~ spl13_10
    | ~ spl13_21
    | ~ spl13_23
    | ~ spl13_30 ),
    inference(forward_demodulation,[],[f351,f210])).

fof(f210,plain,
    ( sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f209])).

fof(f351,plain,
    ( k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) = sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))
    | ~ spl13_10
    | ~ spl13_21
    | ~ spl13_30 ),
    inference(resolution,[],[f343,f204])).

fof(f204,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),X2),sK1)
        | k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) = X2 )
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(resolution,[],[f197,f135])).

fof(f135,plain,
    ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1))
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f196])).

fof(f343,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))),sK1)
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f342])).

fof(f344,plain,
    ( spl13_30
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f337,f150,f100,f92,f342])).

fof(f337,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))),sK1)
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_13 ),
    inference(resolution,[],[f334,f151])).

fof(f151,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0))
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f150])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))
        | r2_hidden(k4_tarski(X0,sK5(sK1,sK0,X0,X1)),sK1) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f332,f93])).

fof(f332,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X5)
        | r2_hidden(k4_tarski(X3,sK5(X5,sK0,X3,X4)),X5)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X5,sK0)) )
    | ~ spl13_6 ),
    inference(resolution,[],[f103,f101])).

fof(f103,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f71,f58])).

fof(f71,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f211,plain,
    ( spl13_23
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(avatar_split_clause,[],[f205,f196,f134,f128,f209])).

fof(f128,plain,
    ( spl13_9
  <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f205,plain,
    ( sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(resolution,[],[f204,f129])).

fof(f129,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1)
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f198,plain,
    ( ~ spl13_4
    | spl13_21
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f193,f88,f196,f92])).

fof(f88,plain,
    ( spl13_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X1
        | ~ v1_relat_1(sK1) )
    | ~ spl13_3 ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,
    ( v1_funct_1(sK1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f152,plain,
    ( spl13_13
    | ~ spl13_2
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f143,f134,f84,f150])).

fof(f84,plain,
    ( spl13_2
  <=> k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f143,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0))
    | ~ spl13_2
    | ~ spl13_10 ),
    inference(resolution,[],[f135,f110])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,sK12(k5_relat_1(sK1,sK0),X0)),k5_relat_1(sK1,sK0)) )
    | ~ spl13_2 ),
    inference(superposition,[],[f78,f85])).

fof(f85,plain,
    ( k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f78,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f136,plain,
    ( spl13_10
    | ~ spl13_9 ),
    inference(avatar_split_clause,[],[f131,f128,f134])).

fof(f131,plain,
    ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1))
    | ~ spl13_9 ),
    inference(resolution,[],[f129,f77])).

fof(f130,plain,
    ( spl13_9
    | spl13_1 ),
    inference(avatar_split_clause,[],[f126,f80,f128])).

fof(f126,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1)
    | spl13_1 ),
    inference(resolution,[],[f108,f81])).

fof(f81,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK9(X0,sK6(k2_relat_1(X0),X1)),sK6(k2_relat_1(X0),X1)),X0) ) ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f102,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).

fof(f18,plain,
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

fof(f19,plain,
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

fof(f94,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f46,f84])).

fof(f46,plain,(
    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f47,f80])).

fof(f47,plain,(
    ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (17059)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.46  % (17051)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (17040)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (17041)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (17043)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (17058)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (17050)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (17062)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (17064)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (17037)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.53  % (17036)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.53  % (17065)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.53  % (17039)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.53  % (17042)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.53  % (17058)Refutation not found, incomplete strategy% (17058)------------------------------
% 1.41/0.53  % (17058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.53  % (17058)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.53  
% 1.41/0.53  % (17058)Memory used [KB]: 10746
% 1.41/0.53  % (17058)Time elapsed: 0.101 s
% 1.41/0.53  % (17058)------------------------------
% 1.41/0.53  % (17058)------------------------------
% 1.41/0.54  % (17047)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.54  % (17038)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.54  % (17056)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.54  % (17054)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.54  % (17044)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.54  % (17061)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (17057)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (17046)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (17048)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (17052)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (17063)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.55  % (17049)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.55  % (17055)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.55  % (17045)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.52/0.55  % (17060)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.56  % (17038)Refutation not found, incomplete strategy% (17038)------------------------------
% 1.52/0.56  % (17038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (17038)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (17038)Memory used [KB]: 10746
% 1.52/0.56  % (17038)Time elapsed: 0.153 s
% 1.52/0.56  % (17038)------------------------------
% 1.52/0.56  % (17038)------------------------------
% 1.52/0.56  % (17053)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.58  % (17055)Refutation found. Thanks to Tanya!
% 1.52/0.58  % SZS status Theorem for theBenchmark
% 1.52/0.60  % SZS output start Proof for theBenchmark
% 1.52/0.60  fof(f427,plain,(
% 1.52/0.60    $false),
% 1.52/0.60    inference(avatar_sat_refutation,[],[f82,f86,f90,f94,f102,f130,f136,f152,f198,f211,f344,f360,f413,f418])).
% 1.52/0.60  fof(f418,plain,(
% 1.52/0.60    spl13_1 | ~spl13_38),
% 1.52/0.60    inference(avatar_split_clause,[],[f414,f411,f80])).
% 1.52/0.60  fof(f80,plain,(
% 1.52/0.60    spl13_1 <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.52/0.60  fof(f411,plain,(
% 1.52/0.60    spl13_38 <=> r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).
% 1.52/0.60  fof(f414,plain,(
% 1.52/0.60    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | ~spl13_38),
% 1.52/0.60    inference(resolution,[],[f412,f60])).
% 1.52/0.60  fof(f60,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f29])).
% 1.52/0.60  fof(f29,plain,(
% 1.52/0.60    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.52/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f28])).
% 1.52/0.60  fof(f28,plain,(
% 1.52/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f17,plain,(
% 1.52/0.60    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.52/0.60    inference(ennf_transformation,[],[f9])).
% 1.52/0.60  fof(f9,plain,(
% 1.52/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.52/0.60    inference(unused_predicate_definition_removal,[],[f1])).
% 1.52/0.60  fof(f1,axiom,(
% 1.52/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.60  fof(f412,plain,(
% 1.52/0.60    r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0)) | ~spl13_38),
% 1.52/0.60    inference(avatar_component_clause,[],[f411])).
% 1.52/0.60  fof(f413,plain,(
% 1.52/0.60    ~spl13_13 | spl13_38 | ~spl13_4 | ~spl13_6 | ~spl13_33),
% 1.52/0.60    inference(avatar_split_clause,[],[f409,f358,f100,f92,f411,f150])).
% 1.52/0.60  fof(f150,plain,(
% 1.52/0.60    spl13_13 <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 1.52/0.60  fof(f92,plain,(
% 1.52/0.60    spl13_4 <=> v1_relat_1(sK1)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 1.52/0.60  fof(f100,plain,(
% 1.52/0.60    spl13_6 <=> v1_relat_1(sK0)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 1.52/0.60  fof(f358,plain,(
% 1.52/0.60    spl13_33 <=> sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).
% 1.52/0.60  fof(f409,plain,(
% 1.52/0.60    r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0)) | (~spl13_4 | ~spl13_6 | ~spl13_33)),
% 1.52/0.60    inference(superposition,[],[f384,f359])).
% 1.52/0.60  fof(f359,plain,(
% 1.52/0.60    sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))) | ~spl13_33),
% 1.52/0.60    inference(avatar_component_clause,[],[f358])).
% 1.52/0.60  fof(f384,plain,(
% 1.52/0.60    ( ! [X2,X3] : (r2_hidden(sK5(sK1,sK0,X2,X3),k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(sK1,sK0))) ) | (~spl13_4 | ~spl13_6)),
% 1.52/0.60    inference(resolution,[],[f380,f77])).
% 1.52/0.60  fof(f77,plain,(
% 1.52/0.60    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.52/0.60    inference(equality_resolution,[],[f66])).
% 1.52/0.60  fof(f66,plain,(
% 1.52/0.60    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.52/0.60    inference(cnf_transformation,[],[f41])).
% 1.52/0.60  fof(f41,plain,(
% 1.52/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.52/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f37,f40,f39,f38])).
% 1.52/0.60  fof(f38,plain,(
% 1.52/0.60    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f39,plain,(
% 1.52/0.60    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f40,plain,(
% 1.52/0.60    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f37,plain,(
% 1.52/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.52/0.60    inference(rectify,[],[f36])).
% 1.52/0.60  fof(f36,plain,(
% 1.52/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.52/0.60    inference(nnf_transformation,[],[f2])).
% 1.52/0.60  fof(f2,axiom,(
% 1.52/0.60    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.52/0.60  fof(f380,plain,(
% 1.52/0.60    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(sK1,sK0,X0,X1),X1),sK0) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))) ) | (~spl13_4 | ~spl13_6)),
% 1.52/0.60    inference(resolution,[],[f378,f93])).
% 1.52/0.60  fof(f93,plain,(
% 1.52/0.60    v1_relat_1(sK1) | ~spl13_4),
% 1.52/0.60    inference(avatar_component_clause,[],[f92])).
% 1.52/0.60  fof(f378,plain,(
% 1.52/0.60    ( ! [X4,X5,X3] : (~v1_relat_1(X5) | r2_hidden(k4_tarski(sK5(X5,sK0,X3,X4),X4),sK0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X5,sK0))) ) | ~spl13_6),
% 1.52/0.60    inference(resolution,[],[f104,f101])).
% 1.52/0.60  fof(f101,plain,(
% 1.52/0.60    v1_relat_1(sK0) | ~spl13_6),
% 1.52/0.60    inference(avatar_component_clause,[],[f100])).
% 1.52/0.60  fof(f104,plain,(
% 1.52/0.60    ( ! [X0,X8,X7,X1] : (~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(subsumption_resolution,[],[f70,f58])).
% 1.52/0.60  fof(f58,plain,(
% 1.52/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f16])).
% 1.52/0.60  fof(f16,plain,(
% 1.52/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(flattening,[],[f15])).
% 1.52/0.60  fof(f15,plain,(
% 1.52/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.52/0.60    inference(ennf_transformation,[],[f5])).
% 1.52/0.60  fof(f5,axiom,(
% 1.52/0.60    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.52/0.60  fof(f70,plain,(
% 1.52/0.60    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(equality_resolution,[],[f49])).
% 1.52/0.60  fof(f49,plain,(
% 1.52/0.60    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f26])).
% 1.52/0.60  fof(f26,plain,(
% 1.52/0.60    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 1.52/0.60  fof(f23,plain,(
% 1.52/0.60    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f24,plain,(
% 1.52/0.60    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f25,plain,(
% 1.52/0.60    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f22,plain,(
% 1.52/0.60    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(rectify,[],[f21])).
% 1.52/0.60  fof(f21,plain,(
% 1.52/0.60    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(nnf_transformation,[],[f12])).
% 1.52/0.60  fof(f12,plain,(
% 1.52/0.60    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(ennf_transformation,[],[f4])).
% 1.52/0.60  fof(f4,axiom,(
% 1.52/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 1.52/0.60  fof(f360,plain,(
% 1.52/0.60    spl13_33 | ~spl13_10 | ~spl13_21 | ~spl13_23 | ~spl13_30),
% 1.52/0.60    inference(avatar_split_clause,[],[f356,f342,f209,f196,f134,f358])).
% 1.52/0.60  fof(f134,plain,(
% 1.52/0.60    spl13_10 <=> r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 1.52/0.60  fof(f196,plain,(
% 1.52/0.60    spl13_21 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).
% 1.52/0.60  fof(f209,plain,(
% 1.52/0.60    spl13_23 <=> sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).
% 1.52/0.60  fof(f342,plain,(
% 1.52/0.60    spl13_30 <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))),sK1)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).
% 1.52/0.60  fof(f356,plain,(
% 1.52/0.60    sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))) | (~spl13_10 | ~spl13_21 | ~spl13_23 | ~spl13_30)),
% 1.52/0.60    inference(forward_demodulation,[],[f351,f210])).
% 1.52/0.60  fof(f210,plain,(
% 1.52/0.60    sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) | ~spl13_23),
% 1.52/0.60    inference(avatar_component_clause,[],[f209])).
% 1.52/0.60  fof(f351,plain,(
% 1.52/0.60    k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) = sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))) | (~spl13_10 | ~spl13_21 | ~spl13_30)),
% 1.52/0.60    inference(resolution,[],[f343,f204])).
% 1.52/0.60  fof(f204,plain,(
% 1.52/0.60    ( ! [X2] : (~r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),X2),sK1) | k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) = X2) ) | (~spl13_10 | ~spl13_21)),
% 1.52/0.60    inference(resolution,[],[f197,f135])).
% 1.52/0.60  fof(f135,plain,(
% 1.52/0.60    r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1)) | ~spl13_10),
% 1.52/0.60    inference(avatar_component_clause,[],[f134])).
% 1.52/0.60  fof(f197,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK1)) ) | ~spl13_21),
% 1.52/0.60    inference(avatar_component_clause,[],[f196])).
% 1.52/0.60  fof(f343,plain,(
% 1.52/0.60    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))),sK1) | ~spl13_30),
% 1.52/0.60    inference(avatar_component_clause,[],[f342])).
% 1.52/0.60  fof(f344,plain,(
% 1.52/0.60    spl13_30 | ~spl13_4 | ~spl13_6 | ~spl13_13),
% 1.52/0.60    inference(avatar_split_clause,[],[f337,f150,f100,f92,f342])).
% 1.52/0.60  fof(f337,plain,(
% 1.52/0.60    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK5(sK1,sK0,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))))),sK1) | (~spl13_4 | ~spl13_6 | ~spl13_13)),
% 1.52/0.60    inference(resolution,[],[f334,f151])).
% 1.52/0.60  fof(f151,plain,(
% 1.52/0.60    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0)) | ~spl13_13),
% 1.52/0.60    inference(avatar_component_clause,[],[f150])).
% 1.52/0.60  fof(f334,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) | r2_hidden(k4_tarski(X0,sK5(sK1,sK0,X0,X1)),sK1)) ) | (~spl13_4 | ~spl13_6)),
% 1.52/0.60    inference(resolution,[],[f332,f93])).
% 1.52/0.60  fof(f332,plain,(
% 1.52/0.60    ( ! [X4,X5,X3] : (~v1_relat_1(X5) | r2_hidden(k4_tarski(X3,sK5(X5,sK0,X3,X4)),X5) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X5,sK0))) ) | ~spl13_6),
% 1.52/0.60    inference(resolution,[],[f103,f101])).
% 1.52/0.60  fof(f103,plain,(
% 1.52/0.60    ( ! [X0,X8,X7,X1] : (~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(subsumption_resolution,[],[f71,f58])).
% 1.52/0.60  fof(f71,plain,(
% 1.52/0.60    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(equality_resolution,[],[f48])).
% 1.52/0.60  fof(f48,plain,(
% 1.52/0.60    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f26])).
% 1.52/0.60  fof(f211,plain,(
% 1.52/0.60    spl13_23 | ~spl13_9 | ~spl13_10 | ~spl13_21),
% 1.52/0.60    inference(avatar_split_clause,[],[f205,f196,f134,f128,f209])).
% 1.52/0.60  fof(f128,plain,(
% 1.52/0.60    spl13_9 <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 1.52/0.60  fof(f205,plain,(
% 1.52/0.60    sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) | (~spl13_9 | ~spl13_10 | ~spl13_21)),
% 1.52/0.60    inference(resolution,[],[f204,f129])).
% 1.52/0.60  fof(f129,plain,(
% 1.52/0.60    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1) | ~spl13_9),
% 1.52/0.60    inference(avatar_component_clause,[],[f128])).
% 1.52/0.60  fof(f198,plain,(
% 1.52/0.60    ~spl13_4 | spl13_21 | ~spl13_3),
% 1.52/0.60    inference(avatar_split_clause,[],[f193,f88,f196,f92])).
% 1.52/0.60  fof(f88,plain,(
% 1.52/0.60    spl13_3 <=> v1_funct_1(sK1)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.52/0.60  fof(f193,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X1 | ~v1_relat_1(sK1)) ) | ~spl13_3),
% 1.52/0.60    inference(resolution,[],[f55,f89])).
% 1.52/0.60  fof(f89,plain,(
% 1.52/0.60    v1_funct_1(sK1) | ~spl13_3),
% 1.52/0.60    inference(avatar_component_clause,[],[f88])).
% 1.52/0.60  fof(f55,plain,(
% 1.52/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = X2 | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f27])).
% 1.52/0.60  fof(f27,plain,(
% 1.52/0.60    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(nnf_transformation,[],[f14])).
% 1.52/0.60  fof(f14,plain,(
% 1.52/0.60    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(flattening,[],[f13])).
% 1.52/0.60  fof(f13,plain,(
% 1.52/0.60    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.60    inference(ennf_transformation,[],[f6])).
% 1.52/0.60  fof(f6,axiom,(
% 1.52/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 1.52/0.60  fof(f152,plain,(
% 1.52/0.60    spl13_13 | ~spl13_2 | ~spl13_10),
% 1.52/0.60    inference(avatar_split_clause,[],[f143,f134,f84,f150])).
% 1.52/0.60  fof(f84,plain,(
% 1.52/0.60    spl13_2 <=> k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.52/0.60  fof(f143,plain,(
% 1.52/0.60    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0)) | (~spl13_2 | ~spl13_10)),
% 1.52/0.60    inference(resolution,[],[f135,f110])).
% 1.52/0.60  fof(f110,plain,(
% 1.52/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,sK12(k5_relat_1(sK1,sK0),X0)),k5_relat_1(sK1,sK0))) ) | ~spl13_2),
% 1.52/0.60    inference(superposition,[],[f78,f85])).
% 1.52/0.60  fof(f85,plain,(
% 1.52/0.60    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) | ~spl13_2),
% 1.52/0.60    inference(avatar_component_clause,[],[f84])).
% 1.52/0.60  fof(f78,plain,(
% 1.52/0.60    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)) )),
% 1.52/0.60    inference(equality_resolution,[],[f65])).
% 1.52/0.60  fof(f65,plain,(
% 1.52/0.60    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.52/0.60    inference(cnf_transformation,[],[f41])).
% 1.52/0.60  fof(f136,plain,(
% 1.52/0.60    spl13_10 | ~spl13_9),
% 1.52/0.60    inference(avatar_split_clause,[],[f131,f128,f134])).
% 1.52/0.60  fof(f131,plain,(
% 1.52/0.60    r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1)) | ~spl13_9),
% 1.52/0.60    inference(resolution,[],[f129,f77])).
% 1.52/0.60  fof(f130,plain,(
% 1.52/0.60    spl13_9 | spl13_1),
% 1.52/0.60    inference(avatar_split_clause,[],[f126,f80,f128])).
% 1.52/0.60  fof(f126,plain,(
% 1.52/0.60    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1) | spl13_1),
% 1.52/0.60    inference(resolution,[],[f108,f81])).
% 1.52/0.60  fof(f81,plain,(
% 1.52/0.60    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | spl13_1),
% 1.52/0.60    inference(avatar_component_clause,[],[f80])).
% 1.52/0.60  fof(f108,plain,(
% 1.52/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),X1) | r2_hidden(k4_tarski(sK9(X0,sK6(k2_relat_1(X0),X1)),sK6(k2_relat_1(X0),X1)),X0)) )),
% 1.52/0.60    inference(resolution,[],[f76,f59])).
% 1.52/0.60  fof(f59,plain,(
% 1.52/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f29])).
% 1.52/0.60  fof(f76,plain,(
% 1.52/0.60    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)) )),
% 1.52/0.60    inference(equality_resolution,[],[f61])).
% 1.52/0.60  fof(f61,plain,(
% 1.52/0.60    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.52/0.60    inference(cnf_transformation,[],[f35])).
% 1.52/0.60  fof(f35,plain,(
% 1.52/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.52/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f31,f34,f33,f32])).
% 1.52/0.60  fof(f32,plain,(
% 1.52/0.60    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f33,plain,(
% 1.52/0.60    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f34,plain,(
% 1.52/0.60    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f31,plain,(
% 1.52/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.52/0.60    inference(rectify,[],[f30])).
% 1.52/0.60  fof(f30,plain,(
% 1.52/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.52/0.60    inference(nnf_transformation,[],[f3])).
% 1.52/0.60  fof(f3,axiom,(
% 1.52/0.60    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.52/0.60  fof(f102,plain,(
% 1.52/0.60    spl13_6),
% 1.52/0.60    inference(avatar_split_clause,[],[f42,f100])).
% 1.52/0.60  fof(f42,plain,(
% 1.52/0.60    v1_relat_1(sK0)),
% 1.52/0.60    inference(cnf_transformation,[],[f20])).
% 1.52/0.60  fof(f20,plain,(
% 1.52/0.60    (~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.52/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).
% 1.52/0.60  fof(f18,plain,(
% 1.52/0.60    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f19,plain,(
% 1.52/0.60    ? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f11,plain,(
% 1.52/0.60    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.52/0.60    inference(flattening,[],[f10])).
% 1.52/0.60  fof(f10,plain,(
% 1.52/0.60    ? [X0] : (? [X1] : ((~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.52/0.60    inference(ennf_transformation,[],[f8])).
% 1.52/0.60  fof(f8,negated_conjecture,(
% 1.52/0.60    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.52/0.60    inference(negated_conjecture,[],[f7])).
% 1.52/0.60  fof(f7,conjecture,(
% 1.52/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 1.52/0.60  fof(f94,plain,(
% 1.52/0.60    spl13_4),
% 1.52/0.60    inference(avatar_split_clause,[],[f44,f92])).
% 1.52/0.60  fof(f44,plain,(
% 1.52/0.60    v1_relat_1(sK1)),
% 1.52/0.60    inference(cnf_transformation,[],[f20])).
% 1.52/0.60  fof(f90,plain,(
% 1.52/0.60    spl13_3),
% 1.52/0.60    inference(avatar_split_clause,[],[f45,f88])).
% 1.52/0.60  fof(f45,plain,(
% 1.52/0.60    v1_funct_1(sK1)),
% 1.52/0.60    inference(cnf_transformation,[],[f20])).
% 1.52/0.60  fof(f86,plain,(
% 1.52/0.60    spl13_2),
% 1.52/0.60    inference(avatar_split_clause,[],[f46,f84])).
% 1.52/0.60  fof(f46,plain,(
% 1.52/0.60    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)),
% 1.52/0.60    inference(cnf_transformation,[],[f20])).
% 1.52/0.60  fof(f82,plain,(
% 1.52/0.60    ~spl13_1),
% 1.52/0.60    inference(avatar_split_clause,[],[f47,f80])).
% 1.52/0.60  fof(f47,plain,(
% 1.52/0.60    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 1.52/0.60    inference(cnf_transformation,[],[f20])).
% 1.52/0.60  % SZS output end Proof for theBenchmark
% 1.52/0.60  % (17055)------------------------------
% 1.52/0.60  % (17055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.60  % (17055)Termination reason: Refutation
% 1.52/0.60  
% 1.52/0.60  % (17055)Memory used [KB]: 11129
% 1.52/0.60  % (17055)Time elapsed: 0.195 s
% 1.52/0.60  % (17055)------------------------------
% 1.52/0.60  % (17055)------------------------------
% 1.52/0.60  % (17035)Success in time 0.244 s
%------------------------------------------------------------------------------
