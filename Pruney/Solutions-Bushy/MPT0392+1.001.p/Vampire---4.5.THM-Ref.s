%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0392+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:54 EST 2020

% Result     : Theorem 35.54s
% Output     : Refutation 35.68s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 377 expanded)
%              Number of leaves         :   20 ( 116 expanded)
%              Depth                    :   16
%              Number of atoms          :  501 (2032 expanded)
%              Number of equality atoms :  107 ( 554 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3867,f4199,f14563,f14993,f28142])).

fof(f28142,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f28141])).

fof(f28141,plain,
    ( $false
    | spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f28128,f17119])).

fof(f17119,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(sK0,sK1),sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))),sK1)
    | spl8_1
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f44,f4239,f15183,f84])).

fof(f84,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK3(X0,X1),sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),X0) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK3(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK5(X0,X5))
                    & r2_hidden(sK5(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK3(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK3(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK3(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK5(X0,X5))
        & r2_hidden(sK5(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f15183,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),sK5(k2_xboole_0(sK0,sK1),sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))))
    | spl8_1
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f174,f190,f82])).

fof(f82,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK5(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK5(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f190,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1)))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl8_5
  <=> r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f174,plain,
    ( k1_xboole_0 != k2_xboole_0(sK0,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f4239,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | spl8_5 ),
    inference(subsumption_resolution,[],[f203,f190])).

fof(f203,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X1] :
      ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != X1
      | r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),X1),k1_setfam_1(sK1))
      | r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),X1),X1) ) ),
    inference(superposition,[],[f45,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f45,plain,(
    k1_setfam_1(k2_xboole_0(sK0,sK1)) != k3_xboole_0(k1_setfam_1(sK0),k1_setfam_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != k3_xboole_0(k1_setfam_1(sK0),k1_setfam_1(sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != k3_xboole_0(k1_setfam_1(sK0),k1_setfam_1(sK1))
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f28128,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))),sK1)
    | spl8_1
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f15184,f17118,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & ~ r2_hidden(sK6(X0,X1,X2),X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f17118,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(sK0,sK1),sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))),sK0)
    | spl8_1
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f43,f4487,f15183,f84])).

fof(f4487,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f45,f190,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f15184,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))),k2_xboole_0(sK0,sK1))
    | spl8_1
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f174,f190,f83])).

fof(f83,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK5(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK5(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14993,plain,
    ( spl8_5
    | ~ spl8_33 ),
    inference(avatar_contradiction_clause,[],[f14992])).

fof(f14992,plain,
    ( $false
    | spl8_5
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f14991,f129])).

fof(f129,plain,(
    r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK1)) ),
    inference(superposition,[],[f91,f70])).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f91,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_xboole_0(sK1,X0)),k1_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f69,f44,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f14991,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK1))
    | spl8_5
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f4491,f3891])).

fof(f3891,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f3866,f3866,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3866,plain,
    ( r2_hidden(sK6(sK0,sK1,sK1),sK1)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f3864])).

fof(f3864,plain,
    ( spl8_33
  <=> r2_hidden(sK6(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f4491,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f4239,f190,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f14563,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f14562])).

fof(f14562,plain,
    ( $false
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f14517,f14561])).

fof(f14561,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f14560,f191])).

fof(f191,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f189])).

fof(f14560,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1)))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f640,f14518])).

fof(f14518,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f88,f191,f72])).

fof(f88,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_xboole_0(sK0,X0)),k1_setfam_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f43,f52])).

fof(f640,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0))
    | ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2] :
      ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != X2
      | ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),X2),k1_setfam_1(sK1))
      | ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),X2),k1_setfam_1(sK0))
      | ~ r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),X2),X2) ) ),
    inference(superposition,[],[f45,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14517,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f124,f191,f72])).

fof(f124,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_xboole_0(X0,sK1)),k1_setfam_1(sK1)) ),
    inference(superposition,[],[f91,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f4199,plain,
    ( ~ spl8_1
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f4198])).

fof(f4198,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f4131,f4022])).

fof(f4022,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f3862,f3918,f72])).

fof(f3918,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f44,f3862,f788])).

fof(f788,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK6(sK0,sK1,X1),sK0)
        | k1_xboole_0 = X1
        | ~ r2_hidden(sK6(sK0,sK1,X1),X1) )
    | ~ spl8_1 ),
    inference(superposition,[],[f175,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f175,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f173])).

fof(f3862,plain,
    ( r2_hidden(sK6(sK0,sK1,sK1),sK0)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f3860])).

fof(f3860,plain,
    ( spl8_32
  <=> r2_hidden(sK6(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f4131,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f4081,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4081,plain,
    ( ! [X0] : r2_hidden(sK7(sK0,sK1),X0)
    | ~ spl8_1
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f4071,f70])).

fof(f4071,plain,
    ( ! [X0] : r2_hidden(sK7(sK0,sK1),k2_xboole_0(X0,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f4034,f85])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4034,plain,
    ( r2_hidden(sK7(sK0,sK1),k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f324,f4031,f72])).

fof(f4031,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f4022,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f324,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl8_1 ),
    inference(superposition,[],[f69,f175])).

fof(f3867,plain,
    ( spl8_32
    | spl8_33
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f3858,f173,f3864,f3860])).

fof(f3858,plain,
    ( r2_hidden(sK6(sK0,sK1,sK1),sK1)
    | r2_hidden(sK6(sK0,sK1,sK1),sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f3856,f44])).

fof(f3856,plain,
    ( r2_hidden(sK6(sK0,sK1,sK1),sK1)
    | r2_hidden(sK6(sK0,sK1,sK1),sK0)
    | k1_xboole_0 = sK1
    | ~ spl8_1 ),
    inference(factoring,[],[f787])).

fof(f787,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK0,sK1,X0),sK1)
        | r2_hidden(sK6(sK0,sK1,X0),X0)
        | r2_hidden(sK6(sK0,sK1,X0),sK0)
        | k1_xboole_0 = X0 )
    | ~ spl8_1 ),
    inference(superposition,[],[f175,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

%------------------------------------------------------------------------------
