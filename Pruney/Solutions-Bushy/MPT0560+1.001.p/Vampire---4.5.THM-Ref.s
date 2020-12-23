%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0560+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:12 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 253 expanded)
%              Number of leaves         :   14 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 (1242 expanded)
%              Number of equality atoms :   39 ( 212 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f94,f343,f384])).

fof(f384,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f372,f352])).

fof(f352,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f27,f81,f76,f47])).

fof(f47,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

% (20069)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f76,plain,
    ( ~ r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),k9_relat_1(sK0,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_1
  <=> r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),k9_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f81,plain,
    ( r2_hidden(sK6(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_2
  <=> r2_hidden(sK6(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X1) != k9_relat_1(k7_relat_1(sK0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(sK0,X1) != k9_relat_1(k7_relat_1(sK0,X2),X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f372,plain,
    ( r2_hidden(k4_tarski(sK6(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),sK0)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f27,f50,f93,f45])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f93,plain,
    ( r2_hidden(k4_tarski(sK6(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),k7_relat_1(sK0,sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_3
  <=> r2_hidden(k4_tarski(sK6(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f27,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f343,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f335,f181])).

fof(f181,plain,
    ( ~ r2_hidden(k4_tarski(sK7(sK0,sK1,sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),k7_relat_1(sK0,sK2))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f50,f29,f77,f117,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,
    ( r2_hidden(sK7(sK0,sK1,sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),sK1)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f27,f77,f48])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,
    ( r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),k9_relat_1(sK0,sK1))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f29,plain,(
    k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f335,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1,sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),k7_relat_1(sK0,sK2))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f27,f50,f116,f180,f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f180,plain,
    ( r2_hidden(sK7(sK0,sK1,sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),sK2)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f28,f117,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1,sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f27,f77,f49])).

fof(f49,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f86,f91,f75])).

fof(f86,plain,
    ( r2_hidden(k4_tarski(sK6(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1))),k7_relat_1(sK0,sK2))
    | r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),k9_relat_1(sK0,sK1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( k9_relat_1(sK0,sK1) != X0
      | r2_hidden(k4_tarski(sK6(k7_relat_1(sK0,sK2),sK1,X0),sK5(k7_relat_1(sK0,sK2),sK1,X0)),k7_relat_1(sK0,sK2))
      | r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,X0),X0) ) ),
    inference(subsumption_resolution,[],[f54,f50])).

fof(f54,plain,(
    ! [X0] :
      ( k9_relat_1(sK0,sK1) != X0
      | r2_hidden(k4_tarski(sK6(k7_relat_1(sK0,sK2),sK1,X0),sK5(k7_relat_1(sK0,sK2),sK1,X0)),k7_relat_1(sK0,sK2))
      | r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,X0),X0)
      | ~ v1_relat_1(k7_relat_1(sK0,sK2)) ) ),
    inference(superposition,[],[f29,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f70,f79,f75])).

fof(f70,plain,
    ( r2_hidden(sK6(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),sK1)
    | r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,k9_relat_1(sK0,sK1)),k9_relat_1(sK0,sK1)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X1] :
      ( k9_relat_1(sK0,sK1) != X1
      | r2_hidden(sK6(k7_relat_1(sK0,sK2),sK1,X1),sK1)
      | r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,X1),X1) ) ),
    inference(subsumption_resolution,[],[f55,f50])).

fof(f55,plain,(
    ! [X1] :
      ( k9_relat_1(sK0,sK1) != X1
      | r2_hidden(sK6(k7_relat_1(sK0,sK2),sK1,X1),sK1)
      | r2_hidden(sK5(k7_relat_1(sK0,sK2),sK1,X1),X1)
      | ~ v1_relat_1(k7_relat_1(sK0,sK2)) ) ),
    inference(superposition,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
