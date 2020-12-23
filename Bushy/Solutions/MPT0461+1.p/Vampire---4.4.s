%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t49_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:02 EDT 2019

% Result     : Theorem 4.92s
% Output     : Refutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 212 expanded)
%              Number of leaves         :   14 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  318 (1144 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3701,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f279,f286,f3698])).

fof(f3698,plain,
    ( ~ spl11_12
    | ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f3697])).

fof(f3697,plain,
    ( $false
    | ~ spl11_12
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f3696,f269])).

fof(f269,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK2))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl11_12
  <=> v1_relat_1(k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f3696,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK2))
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f3682,f58])).

fof(f58,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
                & r1_tarski(X0,X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X2))
              & r1_tarski(sK0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(sK1,X2))
            & r1_tarski(X0,sK1)
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
          & r1_tarski(X0,X1)
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X0,sK2),k5_relat_1(X1,sK2))
        & r1_tarski(X0,X1)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
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
               => ( r1_tarski(X0,X1)
                 => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t49_relat_1.p',t49_relat_1)).

fof(f3682,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(k5_relat_1(sK0,sK2))
    | ~ spl11_14 ),
    inference(resolution,[],[f1645,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t49_relat_1.p',d3_relat_1)).

fof(f1645,plain,
    ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),k5_relat_1(sK1,sK2))
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f1636,f55])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1636,plain,
    ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl11_14 ),
    inference(resolution,[],[f753,f412])).

fof(f412,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)))),X5)
        | r2_hidden(k4_tarski(X4,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),k5_relat_1(X5,sK2))
        | ~ v1_relat_1(X5) )
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f410,f56])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f410,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),k5_relat_1(X5,sK2))
        | ~ r2_hidden(k4_tarski(X4,sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)))),X5)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X5) )
    | ~ spl11_14 ),
    inference(resolution,[],[f309,f228])).

fof(f228,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X8),X1)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f81,f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t49_relat_1.p',dt_k5_relat_1)).

fof(f81,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f42,f45,f44,f43])).

fof(f43,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t49_relat_1.p',d8_relat_1)).

fof(f309,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),sK2)
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f308,f54])).

fof(f54,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f308,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f297,f56])).

fof(f297,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl11_14 ),
    inference(resolution,[],[f278,f214])).

fof(f214,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f82,f74])).

fof(f82,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f278,plain,
    ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl11_14
  <=> r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f753,plain,
    ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)))),sK1)
    | ~ spl11_14 ),
    inference(resolution,[],[f392,f57])).

fof(f57,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f392,plain,
    ( ! [X6] :
        ( ~ r1_tarski(sK0,X6)
        | r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)))),X6) )
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f390,f54])).

fof(f390,plain,
    ( ! [X6] :
        ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)))),X6)
        | ~ r1_tarski(sK0,X6)
        | ~ v1_relat_1(sK0) )
    | ~ spl11_14 ),
    inference(resolution,[],[f307,f67])).

fof(f67,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f307,plain,
    ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)))),sK0)
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f306,f54])).

fof(f306,plain,
    ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f296,f56])).

fof(f296,plain,
    ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK6(sK0,sK2,sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)))),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl11_14 ),
    inference(resolution,[],[f278,f221])).

fof(f221,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f83,f74])).

fof(f83,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f286,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f284,f54])).

fof(f284,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f281,f56])).

fof(f281,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl11_13 ),
    inference(resolution,[],[f272,f74])).

fof(f272,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK2))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl11_13
  <=> ~ v1_relat_1(k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f279,plain,
    ( ~ spl11_13
    | spl11_14 ),
    inference(avatar_split_clause,[],[f183,f277,f271])).

fof(f183,plain,
    ( r2_hidden(k4_tarski(sK7(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)),sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ v1_relat_1(k5_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f68,f58])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
