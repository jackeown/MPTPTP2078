%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t50_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:03 EDT 2019

% Result     : Theorem 5.36s
% Output     : Refutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 256 expanded)
%              Number of leaves         :   17 ( 102 expanded)
%              Depth                    :   16
%              Number of atoms          :  358 (1709 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10549,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f270,f277,f10504,f10548])).

fof(f10548,plain,
    ( ~ spl12_14
    | spl12_171 ),
    inference(avatar_contradiction_clause,[],[f10546])).

fof(f10546,plain,
    ( $false
    | ~ spl12_14
    | ~ spl12_171 ),
    inference(unit_resulting_resolution,[],[f56,f58,f860,f864,f10442,f226])).

fof(f226,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X8),X1)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f84,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t50_relat_1.p',dt_k5_relat_1)).

fof(f84,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f43,f46,f45,f44])).

fof(f44,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t50_relat_1.p',d8_relat_1)).

fof(f10442,plain,
    ( ~ r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),k5_relat_1(sK1,sK3))
    | ~ spl12_171 ),
    inference(avatar_component_clause,[],[f10441])).

fof(f10441,plain,
    ( spl12_171
  <=> ~ r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_171])])).

fof(f864,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK3)
    | ~ spl12_14 ),
    inference(resolution,[],[f441,f60])).

fof(f60,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(sK1,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(X0,sK1)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(X0,X1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(X0,sK2),k5_relat_1(X1,X3))
            & r1_tarski(sK2,X3)
            & r1_tarski(X0,X1)
            & v1_relat_1(X3) )
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,sK3))
        & r1_tarski(X2,sK3)
        & r1_tarski(X0,X1)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t50_relat_1.p',t50_relat_1)).

fof(f441,plain,
    ( ! [X6] :
        ( ~ r1_tarski(sK2,X6)
        | r2_hidden(k4_tarski(sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),X6) )
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f439,f57])).

fof(f57,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f439,plain,
    ( ! [X6] :
        ( r2_hidden(k4_tarski(sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),X6)
        | ~ r1_tarski(sK2,X6)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_14 ),
    inference(resolution,[],[f295,f70])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t50_relat_1.p',d3_relat_1)).

fof(f295,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK2)
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f294,f55])).

fof(f55,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f294,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f283,f57])).

fof(f283,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl12_14 ),
    inference(resolution,[],[f269,f214])).

fof(f214,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f85,f77])).

fof(f85,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f269,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),k5_relat_1(sK0,sK2))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl12_14
  <=> r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f860,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)))),sK1)
    | ~ spl12_14 ),
    inference(resolution,[],[f422,f59])).

fof(f59,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f422,plain,
    ( ! [X6] :
        ( ~ r1_tarski(sK0,X6)
        | r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)))),X6) )
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f420,f55])).

fof(f420,plain,
    ( ! [X6] :
        ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)))),X6)
        | ~ r1_tarski(sK0,X6)
        | ~ v1_relat_1(sK0) )
    | ~ spl12_14 ),
    inference(resolution,[],[f293,f70])).

fof(f293,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)))),sK0)
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f292,f55])).

fof(f292,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f282,f57])).

fof(f282,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK7(sK0,sK2,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)))),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl12_14 ),
    inference(resolution,[],[f269,f219])).

fof(f219,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f86,f77])).

fof(f86,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f58,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f10504,plain,
    ( ~ spl12_12
    | ~ spl12_170 ),
    inference(avatar_contradiction_clause,[],[f10503])).

fof(f10503,plain,
    ( $false
    | ~ spl12_12
    | ~ spl12_170 ),
    inference(subsumption_resolution,[],[f10502,f260])).

fof(f260,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK2))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl12_12
  <=> v1_relat_1(k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f10502,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK2))
    | ~ spl12_170 ),
    inference(subsumption_resolution,[],[f10488,f61])).

fof(f61,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f10488,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    | ~ v1_relat_1(k5_relat_1(sK0,sK2))
    | ~ spl12_170 ),
    inference(resolution,[],[f10445,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10445,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),k5_relat_1(sK1,sK3))
    | ~ spl12_170 ),
    inference(avatar_component_clause,[],[f10444])).

fof(f10444,plain,
    ( spl12_170
  <=> r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_170])])).

fof(f277,plain,(
    spl12_13 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f275,f55])).

fof(f275,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f272,f57])).

fof(f272,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl12_13 ),
    inference(resolution,[],[f263,f77])).

fof(f263,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK2))
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl12_13
  <=> ~ v1_relat_1(k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f270,plain,
    ( ~ spl12_13
    | spl12_14 ),
    inference(avatar_split_clause,[],[f183,f268,f262])).

fof(f183,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),k5_relat_1(sK0,sK2))
    | ~ v1_relat_1(k5_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f71,f61])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
