%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0393+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 240 expanded)
%              Number of leaves         :   11 (  73 expanded)
%              Depth                    :   25
%              Number of atoms          :  242 (1472 expanded)
%              Number of equality atoms :  112 ( 672 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(resolution,[],[f234,f41])).

fof(f41,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f234,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(subsumption_resolution,[],[f227,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f227,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f219,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f219,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f76,f187])).

fof(f187,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f186,f176])).

fof(f176,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f173,f40])).

fof(f40,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).

fof(f19,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f173,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f49,f167])).

fof(f167,plain,
    ( sK0 = sK3(k1_tarski(sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f166,f147])).

fof(f147,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK3(k1_tarski(sK0),sK0) ),
    inference(resolution,[],[f146,f77])).

fof(f77,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f146,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2] :
      ( sK0 != X2
      | r2_hidden(sK3(k1_tarski(sK0),X2),k1_tarski(sK0))
      | ~ r2_hidden(sK2(k1_tarski(sK0),X2),X2)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f40,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),X0) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK4(X0,X5))
                    & r2_hidden(sK4(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).

fof(f25,plain,(
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
              ( ~ r2_hidden(sK2(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK2(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK4(X0,X5))
        & r2_hidden(sK4(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f166,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK3(k1_tarski(sK0),sK0)
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f165,f76])).

fof(f165,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK3(k1_tarski(sK0),sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f164,f40])).

fof(f164,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK3(k1_tarski(sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK3(k1_tarski(sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f147,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f186,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f185,f76])).

fof(f185,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f184,f40])).

fof(f184,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f176,f47])).

fof(f76,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

%------------------------------------------------------------------------------
