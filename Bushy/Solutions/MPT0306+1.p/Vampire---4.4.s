%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t118_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:58 EDT 2019

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 190 expanded)
%              Number of leaves         :   10 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  238 (1146 expanded)
%              Number of equality atoms :   36 ( 240 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7465,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f2285,f7450])).

fof(f7450,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f7449])).

fof(f7449,plain,
    ( $false
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f7448,f59])).

fof(f59,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl9_1
  <=> ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f7448,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f7371,f2286])).

fof(f2286,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK0,sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t118_zfmisc_1.p',d3_tarski)).

fof(f7371,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK0,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f2546,f2306])).

fof(f2306,plain,
    ( r2_hidden(sK7(sK0,sK2,sK3(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f2297,f31])).

fof(f31,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) )
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
          | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
        & r1_tarski(X0,X1) )
   => ( ( ~ r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
        | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
          & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t118_zfmisc_1.p',t118_zfmisc_1)).

fof(f2297,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_hidden(sK7(sK0,sK2,sK3(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),X0) )
    | ~ spl9_1 ),
    inference(resolution,[],[f2293,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2293,plain,
    ( r2_hidden(sK7(sK0,sK2,sK3(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f2286,f53])).

fof(f53,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK7(X0,X1,X8),X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = sK4(X0,X1,X2)
              & r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
                & r2_hidden(sK8(X0,X1,X8),X1)
                & r2_hidden(sK7(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f26,f29,f28,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X3
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t118_zfmisc_1.p',d2_zfmisc_1)).

fof(f2546,plain,(
    ! [X19,X17,X20,X18] :
      ( ~ r2_hidden(sK7(X17,X18,sK3(X19,k2_zfmisc_1(X20,X18))),X20)
      | ~ r2_hidden(sK3(X19,k2_zfmisc_1(X20,X18)),k2_zfmisc_1(X17,X18))
      | r1_tarski(X19,k2_zfmisc_1(X20,X18)) ) ),
    inference(resolution,[],[f1281,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1281,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK7(X3,X2,X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X2)) ) ),
    inference(duplicate_literal_removal,[],[f1278])).

fof(f1278,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK7(X3,X2,X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X2)) ) ),
    inference(resolution,[],[f187,f52])).

fof(f52,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f187,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),X4)
      | r2_hidden(X2,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(sK7(X0,X1,X2),X3)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2285,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f2284])).

fof(f2284,plain,
    ( $false
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f2279,f65])).

fof(f65,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl9_3
  <=> ~ r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f2279,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_3 ),
    inference(resolution,[],[f2275,f38])).

fof(f2275,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f2269,f2150])).

fof(f2150,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK0))
    | ~ spl9_3 ),
    inference(resolution,[],[f65,f37])).

fof(f2269,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ r2_hidden(sK3(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK0))
    | ~ spl9_3 ),
    inference(resolution,[],[f1280,f2161])).

fof(f2161,plain,
    ( r2_hidden(sK7(sK2,sK0,sK3(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),sK2)
    | ~ spl9_3 ),
    inference(resolution,[],[f2150,f53])).

fof(f1280,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK7(X6,sK0,X4),X5)
      | r2_hidden(X4,k2_zfmisc_1(X5,sK1))
      | ~ r2_hidden(X4,k2_zfmisc_1(X6,sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1279])).

fof(f1279,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(X4,k2_zfmisc_1(X5,sK1))
      | ~ r2_hidden(sK7(X6,sK0,X4),X5)
      | ~ r2_hidden(X4,k2_zfmisc_1(X6,sK0))
      | ~ r2_hidden(X4,k2_zfmisc_1(X6,sK0)) ) ),
    inference(resolution,[],[f187,f836])).

fof(f836,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK8(X4,sK0,X5),sK1)
      | ~ r2_hidden(X5,k2_zfmisc_1(X4,sK0)) ) ),
    inference(resolution,[],[f87,f31])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r2_hidden(sK8(X1,X2,X0),X3)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f52,f36])).

fof(f66,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f32,f64,f58])).

fof(f32,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
