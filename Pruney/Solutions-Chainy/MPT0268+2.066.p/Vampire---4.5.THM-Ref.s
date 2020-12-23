%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:45 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 447 expanded)
%              Number of leaves         :   11 ( 121 expanded)
%              Depth                    :   23
%              Number of atoms          :  239 (1885 expanded)
%              Number of equality atoms :   67 ( 372 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f924,plain,(
    $false ),
    inference(subsumption_resolution,[],[f918,f886])).

fof(f886,plain,(
    r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f39,f885])).

fof(f885,plain,(
    sK1 = k4_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f870,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f870,plain,(
    k4_xboole_0(sK1,k1_tarski(sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f46,f867])).

fof(f867,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f854,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f854,plain,
    ( sP0(k1_tarski(sK2),sK1,k1_xboole_0)
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(superposition,[],[f797,f788])).

fof(f788,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(resolution,[],[f772,f38])).

fof(f38,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK1 = k4_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( r2_hidden(sK2,sK1)
      | sK1 != k4_xboole_0(sK1,k1_tarski(sK2)) )
    & ( ~ r2_hidden(sK2,sK1)
      | sK1 = k4_xboole_0(sK1,k1_tarski(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK2,sK1)
        | sK1 != k4_xboole_0(sK1,k1_tarski(sK2)) )
      & ( ~ r2_hidden(sK2,sK1)
        | sK1 = k4_xboole_0(sK1,k1_tarski(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f772,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,X2)
      | k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3)) ) ),
    inference(duplicate_literal_removal,[],[f753])).

fof(f753,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,X2)
      | k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3))
      | k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3)) ) ),
    inference(superposition,[],[f131,f722])).

fof(f722,plain,(
    ! [X6,X5] :
      ( sK3(k3_xboole_0(X5,k1_tarski(X6))) = X6
      | k1_xboole_0 = k3_xboole_0(X5,k1_tarski(X6)) ) ),
    inference(duplicate_literal_removal,[],[f718])).

fof(f718,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 = k3_xboole_0(X5,k1_tarski(X6))
      | sK3(k3_xboole_0(X5,k1_tarski(X6))) = X6
      | k1_xboole_0 = k3_xboole_0(X5,k1_tarski(X6)) ) ),
    inference(resolution,[],[f714,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k3_xboole_0(X0,X1)),X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f114,f67])).

fof(f67,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X2,X0)
      | r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f49,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f714,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0),k1_tarski(X1))
      | k1_xboole_0 = X0
      | sK3(X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f705])).

fof(f705,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(sK3(X0),k1_tarski(X1))
      | sK3(X0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f704,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),k4_xboole_0(X0,k1_tarski(X1)))
      | sK3(X0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f704,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0),k4_xboole_0(X0,X1))
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK3(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f697])).

fof(f697,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0),k4_xboole_0(X0,X1))
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f236,f505])).

fof(f505,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),k3_xboole_0(X0,X1))
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f211,f67])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | r2_hidden(sK3(X0),X2)
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f42])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f236,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK3(X1),k3_xboole_0(X1,X2))
      | ~ r2_hidden(sK3(X1),k4_xboole_0(X1,X2))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f121,f46])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0),k5_xboole_0(X0,X1))
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f131,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k3_xboole_0(X0,X1)),X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f113,f67])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f797,plain,(
    ! [X4,X5] : sP0(k1_tarski(X5),k4_xboole_0(X4,k1_tarski(X5)),k1_xboole_0) ),
    inference(superposition,[],[f67,f784])).

fof(f784,plain,(
    ! [X30,X31] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X30,k1_tarski(X31)),k1_tarski(X31)) ),
    inference(resolution,[],[f772,f68])).

fof(f68,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(sK2))
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f918,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(superposition,[],[f68,f885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.51  % (582)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (587)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (595)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (606)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (586)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (582)Refutation not found, incomplete strategy% (582)------------------------------
% 0.22/0.52  % (582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (582)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (582)Memory used [KB]: 10618
% 0.22/0.52  % (582)Time elapsed: 0.113 s
% 0.22/0.52  % (582)------------------------------
% 0.22/0.52  % (582)------------------------------
% 0.22/0.53  % (597)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (597)Refutation not found, incomplete strategy% (597)------------------------------
% 0.22/0.53  % (597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (588)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (597)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (597)Memory used [KB]: 10618
% 0.22/0.53  % (597)Time elapsed: 0.118 s
% 0.22/0.53  % (597)------------------------------
% 0.22/0.53  % (597)------------------------------
% 0.22/0.53  % (602)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (602)Refutation not found, incomplete strategy% (602)------------------------------
% 0.22/0.53  % (602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (602)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (602)Memory used [KB]: 10746
% 0.22/0.53  % (602)Time elapsed: 0.106 s
% 0.22/0.53  % (602)------------------------------
% 0.22/0.53  % (602)------------------------------
% 0.22/0.53  % (580)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (583)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (594)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (596)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (593)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (581)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (589)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (601)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (588)Refutation not found, incomplete strategy% (588)------------------------------
% 0.22/0.54  % (588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (588)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (588)Memory used [KB]: 10618
% 0.22/0.54  % (588)Time elapsed: 0.121 s
% 0.22/0.54  % (588)------------------------------
% 0.22/0.54  % (588)------------------------------
% 0.22/0.54  % (590)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (605)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (607)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (585)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (603)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (609)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (584)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.52/0.55  % (600)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.52/0.56  % (591)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.56  % (599)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.56  % (598)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.56  % (608)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.64/0.57  % (604)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.64/0.57  % (592)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.06/0.63  % (611)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.06/0.63  % (587)Refutation found. Thanks to Tanya!
% 2.06/0.63  % SZS status Theorem for theBenchmark
% 2.06/0.63  % SZS output start Proof for theBenchmark
% 2.06/0.63  fof(f924,plain,(
% 2.06/0.63    $false),
% 2.06/0.63    inference(subsumption_resolution,[],[f918,f886])).
% 2.06/0.63  fof(f886,plain,(
% 2.06/0.63    r2_hidden(sK2,sK1)),
% 2.06/0.63    inference(subsumption_resolution,[],[f39,f885])).
% 2.06/0.63  fof(f885,plain,(
% 2.06/0.63    sK1 = k4_xboole_0(sK1,k1_tarski(sK2))),
% 2.06/0.63    inference(forward_demodulation,[],[f870,f40])).
% 2.06/0.63  fof(f40,plain,(
% 2.06/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f7])).
% 2.06/0.63  fof(f7,axiom,(
% 2.06/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.06/0.63  fof(f870,plain,(
% 2.06/0.63    k4_xboole_0(sK1,k1_tarski(sK2)) = k5_xboole_0(sK1,k1_xboole_0)),
% 2.06/0.63    inference(superposition,[],[f46,f867])).
% 2.06/0.63  fof(f867,plain,(
% 2.06/0.63    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK2))),
% 2.06/0.63    inference(subsumption_resolution,[],[f854,f55])).
% 2.06/0.63  fof(f55,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.06/0.63    inference(cnf_transformation,[],[f34])).
% 2.06/0.63  fof(f34,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 2.06/0.63    inference(nnf_transformation,[],[f23])).
% 2.06/0.63  fof(f23,plain,(
% 2.06/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.06/0.63    inference(definition_folding,[],[f1,f22])).
% 2.06/0.63  fof(f22,plain,(
% 2.06/0.63    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.06/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.06/0.63  fof(f1,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.06/0.63  fof(f854,plain,(
% 2.06/0.63    sP0(k1_tarski(sK2),sK1,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK2))),
% 2.06/0.63    inference(superposition,[],[f797,f788])).
% 2.06/0.63  fof(f788,plain,(
% 2.06/0.63    sK1 = k4_xboole_0(sK1,k1_tarski(sK2)) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK2))),
% 2.06/0.63    inference(resolution,[],[f772,f38])).
% 2.06/0.63  fof(f38,plain,(
% 2.06/0.63    ~r2_hidden(sK2,sK1) | sK1 = k4_xboole_0(sK1,k1_tarski(sK2))),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f26,plain,(
% 2.06/0.63    (r2_hidden(sK2,sK1) | sK1 != k4_xboole_0(sK1,k1_tarski(sK2))) & (~r2_hidden(sK2,sK1) | sK1 = k4_xboole_0(sK1,k1_tarski(sK2)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).
% 2.06/0.63  fof(f25,plain,(
% 2.06/0.63    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK2,sK1) | sK1 != k4_xboole_0(sK1,k1_tarski(sK2))) & (~r2_hidden(sK2,sK1) | sK1 = k4_xboole_0(sK1,k1_tarski(sK2))))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f24,plain,(
% 2.06/0.63    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 2.06/0.63    inference(nnf_transformation,[],[f19])).
% 2.06/0.63  fof(f19,plain,(
% 2.06/0.63    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f17])).
% 2.06/0.63  fof(f17,negated_conjecture,(
% 2.06/0.63    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.06/0.63    inference(negated_conjecture,[],[f16])).
% 2.06/0.63  fof(f16,conjecture,(
% 2.06/0.63    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.06/0.63  fof(f772,plain,(
% 2.06/0.63    ( ! [X2,X3] : (r2_hidden(X3,X2) | k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3))) )),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f753])).
% 2.06/0.63  fof(f753,plain,(
% 2.06/0.63    ( ! [X2,X3] : (r2_hidden(X3,X2) | k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3)) | k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3))) )),
% 2.06/0.63    inference(superposition,[],[f131,f722])).
% 2.06/0.63  fof(f722,plain,(
% 2.06/0.63    ( ! [X6,X5] : (sK3(k3_xboole_0(X5,k1_tarski(X6))) = X6 | k1_xboole_0 = k3_xboole_0(X5,k1_tarski(X6))) )),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f718])).
% 2.06/0.63  fof(f718,plain,(
% 2.06/0.63    ( ! [X6,X5] : (k1_xboole_0 = k3_xboole_0(X5,k1_tarski(X6)) | sK3(k3_xboole_0(X5,k1_tarski(X6))) = X6 | k1_xboole_0 = k3_xboole_0(X5,k1_tarski(X6))) )),
% 2.06/0.63    inference(resolution,[],[f714,f135])).
% 2.06/0.63  fof(f135,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r2_hidden(sK3(k3_xboole_0(X0,X1)),X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.06/0.63    inference(resolution,[],[f114,f67])).
% 2.06/0.63  fof(f67,plain,(
% 2.06/0.63    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 2.06/0.63    inference(equality_resolution,[],[f54])).
% 2.06/0.63  fof(f54,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.06/0.63    inference(cnf_transformation,[],[f34])).
% 2.06/0.63  fof(f114,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~sP0(X1,X2,X0) | r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f49,f42])).
% 2.06/0.63  fof(f42,plain,(
% 2.06/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f28])).
% 2.06/0.63  fof(f28,plain,(
% 2.06/0.63    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).
% 2.06/0.63  fof(f27,plain,(
% 2.06/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f20,plain,(
% 2.06/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.06/0.63    inference(ennf_transformation,[],[f4])).
% 2.06/0.63  fof(f4,axiom,(
% 2.06/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.06/0.63  fof(f49,plain,(
% 2.06/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f33])).
% 2.06/0.63  fof(f33,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 2.06/0.63  fof(f32,plain,(
% 2.06/0.63    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f31,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.06/0.63    inference(rectify,[],[f30])).
% 2.06/0.63  fof(f30,plain,(
% 2.06/0.63    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.06/0.63    inference(flattening,[],[f29])).
% 2.06/0.63  fof(f29,plain,(
% 2.06/0.63    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.06/0.63    inference(nnf_transformation,[],[f22])).
% 2.06/0.63  fof(f714,plain,(
% 2.06/0.63    ( ! [X0,X1] : (~r2_hidden(sK3(X0),k1_tarski(X1)) | k1_xboole_0 = X0 | sK3(X0) = X1) )),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f705])).
% 2.06/0.63  fof(f705,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK3(X0),k1_tarski(X1)) | sK3(X0) = X1 | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f704,f183])).
% 2.06/0.63  fof(f183,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0),k4_xboole_0(X0,k1_tarski(X1))) | sK3(X0) = X1 | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f62,f42])).
% 2.06/0.63  fof(f62,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f37])).
% 2.06/0.63  fof(f37,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 2.06/0.63    inference(flattening,[],[f36])).
% 2.06/0.63  fof(f36,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 2.06/0.63    inference(nnf_transformation,[],[f15])).
% 2.06/0.63  fof(f15,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 2.06/0.63  fof(f704,plain,(
% 2.06/0.63    ( ! [X0,X1] : (~r2_hidden(sK3(X0),k4_xboole_0(X0,X1)) | k1_xboole_0 = X0 | ~r2_hidden(sK3(X0),X1)) )),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f697])).
% 2.06/0.63  fof(f697,plain,(
% 2.06/0.63    ( ! [X0,X1] : (~r2_hidden(sK3(X0),k4_xboole_0(X0,X1)) | k1_xboole_0 = X0 | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f236,f505])).
% 2.06/0.63  fof(f505,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0),k3_xboole_0(X0,X1)) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f211,f67])).
% 2.06/0.63  fof(f211,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | r2_hidden(sK3(X0),X2) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f50,f42])).
% 2.06/0.63  fof(f50,plain,(
% 2.06/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f33])).
% 2.06/0.63  fof(f236,plain,(
% 2.06/0.63    ( ! [X2,X1] : (~r2_hidden(sK3(X1),k3_xboole_0(X1,X2)) | ~r2_hidden(sK3(X1),k4_xboole_0(X1,X2)) | k1_xboole_0 = X1) )),
% 2.06/0.63    inference(superposition,[],[f121,f46])).
% 2.06/0.63  fof(f121,plain,(
% 2.06/0.63    ( ! [X0,X1] : (~r2_hidden(sK3(X0),k5_xboole_0(X0,X1)) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f57,f42])).
% 2.06/0.63  fof(f57,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f35])).
% 2.06/0.63  fof(f35,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.06/0.63    inference(nnf_transformation,[],[f21])).
% 2.06/0.63  fof(f21,plain,(
% 2.06/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.06/0.63    inference(ennf_transformation,[],[f3])).
% 2.06/0.63  fof(f3,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.06/0.63  fof(f131,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r2_hidden(sK3(k3_xboole_0(X0,X1)),X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.06/0.63    inference(resolution,[],[f113,f67])).
% 2.06/0.63  fof(f113,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~sP0(X2,X1,X0) | r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f48,f42])).
% 2.06/0.63  fof(f48,plain,(
% 2.06/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f33])).
% 2.06/0.63  fof(f797,plain,(
% 2.06/0.63    ( ! [X4,X5] : (sP0(k1_tarski(X5),k4_xboole_0(X4,k1_tarski(X5)),k1_xboole_0)) )),
% 2.06/0.63    inference(superposition,[],[f67,f784])).
% 2.06/0.63  fof(f784,plain,(
% 2.06/0.63    ( ! [X30,X31] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X30,k1_tarski(X31)),k1_tarski(X31))) )),
% 2.06/0.63    inference(resolution,[],[f772,f68])).
% 2.06/0.63  fof(f68,plain,(
% 2.06/0.63    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.06/0.63    inference(equality_resolution,[],[f61])).
% 2.06/0.63  fof(f61,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f37])).
% 2.06/0.63  fof(f46,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f5])).
% 2.06/0.63  fof(f5,axiom,(
% 2.06/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.06/0.63  fof(f39,plain,(
% 2.06/0.63    sK1 != k4_xboole_0(sK1,k1_tarski(sK2)) | r2_hidden(sK2,sK1)),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f918,plain,(
% 2.06/0.63    ~r2_hidden(sK2,sK1)),
% 2.06/0.63    inference(superposition,[],[f68,f885])).
% 2.06/0.63  % SZS output end Proof for theBenchmark
% 2.06/0.63  % (587)------------------------------
% 2.06/0.63  % (587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (587)Termination reason: Refutation
% 2.06/0.63  
% 2.06/0.63  % (587)Memory used [KB]: 7291
% 2.06/0.63  % (587)Time elapsed: 0.213 s
% 2.06/0.63  % (587)------------------------------
% 2.06/0.63  % (587)------------------------------
% 2.06/0.63  % (579)Success in time 0.269 s
%------------------------------------------------------------------------------
