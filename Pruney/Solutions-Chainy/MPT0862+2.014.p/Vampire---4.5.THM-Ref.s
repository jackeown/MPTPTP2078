%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:28 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   86 (1115 expanded)
%              Number of leaves         :   13 ( 334 expanded)
%              Depth                    :   19
%              Number of atoms          :  254 (2731 expanded)
%              Number of equality atoms :   67 (1251 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f513,plain,(
    $false ),
    inference(resolution,[],[f463,f375])).

fof(f375,plain,(
    r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(subsumption_resolution,[],[f374,f283])).

fof(f283,plain,(
    ! [X0] : ~ r2_hidden(sK5,X0) ),
    inference(resolution,[],[f266,f82])).

fof(f82,plain,(
    r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f58,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5))) ),
    inference(definition_unfolding,[],[f31,f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f56])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( sK5 != k2_mcart_1(sK2)
        & sK4 != k2_mcart_1(sK2) )
      | sK3 != k1_mcart_1(sK2) )
    & r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) )
   => ( ( ( sK5 != k2_mcart_1(sK2)
          & sK4 != k2_mcart_1(sK2) )
        | sK3 != k1_mcart_1(sK2) )
      & r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(sK2),X1)
      | ~ r2_hidden(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f263,f92])).

fof(f92,plain,(
    sK4 != k2_mcart_1(sK2) ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( sK3 != sK3
    | sK4 != k2_mcart_1(sK2) ),
    inference(backward_demodulation,[],[f32,f84])).

fof(f84,plain,(
    sK3 = k1_mcart_1(sK2) ),
    inference(resolution,[],[f60,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f32,plain,
    ( sK4 != k2_mcart_1(sK2)
    | sK3 != k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5,X0)
      | sK4 = k2_mcart_1(sK2)
      | ~ r2_hidden(k2_mcart_1(sK2),X1) ) ),
    inference(resolution,[],[f221,f118])).

fof(f118,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k2_enumset1(X4,X4,X4,X4))
      | X2 = X4
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f87,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f87,plain,(
    ! [X6,X7,X5] :
      ( sP0(k2_enumset1(X6,X6,X6,X6),X5,X7)
      | ~ r2_hidden(X5,X7)
      | X5 = X6 ) ),
    inference(resolution,[],[f61,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f41,f67])).

fof(f67,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f15,f14])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f221,plain,(
    ! [X2] :
      ( r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ r2_hidden(sK5,X2) ) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5,X2)
      | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK4,sK4,sK4,sK4))
      | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ) ),
    inference(resolution,[],[f211,f111])).

fof(f111,plain,(
    ! [X30,X31,X29] :
      ( ~ r2_hidden(X31,k2_enumset1(X29,X29,X29,X30))
      | r2_hidden(X30,k2_enumset1(X31,X31,X31,X31))
      | r2_hidden(X29,k2_enumset1(X31,X31,X31,X31)) ) ),
    inference(superposition,[],[f68,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f55,f56,f56])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f68,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f211,plain,(
    ! [X0] :
      ( r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))
      | ~ r2_hidden(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f208,f93])).

fof(f93,plain,(
    sK5 != k2_mcart_1(sK2) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( sK3 != sK3
    | sK5 != k2_mcart_1(sK2) ),
    inference(backward_demodulation,[],[f33,f84])).

fof(f33,plain,
    ( sK5 != k2_mcart_1(sK2)
    | sK3 != k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f208,plain,(
    ! [X0] :
      ( r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))
      | sK5 = k2_mcart_1(sK2)
      | ~ r2_hidden(sK5,X0) ) ),
    inference(resolution,[],[f161,f118])).

fof(f161,plain,
    ( r2_hidden(sK5,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))
    | r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) ),
    inference(resolution,[],[f111,f82])).

fof(f374,plain,
    ( r2_hidden(sK5,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(resolution,[],[f359,f111])).

fof(f359,plain,(
    r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(resolution,[],[f342,f82])).

fof(f342,plain,(
    ! [X19] :
      ( ~ r2_hidden(k2_mcart_1(sK2),X19)
      | r2_hidden(sK4,X19) ) ),
    inference(subsumption_resolution,[],[f324,f283])).

fof(f324,plain,(
    ! [X19] :
      ( r2_hidden(sK5,X19)
      | r2_hidden(sK4,X19)
      | ~ r2_hidden(k2_mcart_1(sK2),X19) ) ),
    inference(resolution,[],[f186,f82])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
      | r2_hidden(X2,X3)
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X3) ) ),
    inference(resolution,[],[f106,f46])).

fof(f106,plain,(
    ! [X12,X10,X13,X11] :
      ( sP0(X12,X13,k2_enumset1(X10,X10,X10,X11))
      | ~ r2_hidden(X13,k2_enumset1(X10,X10,X10,X11))
      | r2_hidden(X11,X12)
      | r2_hidden(X10,X12) ) ),
    inference(superposition,[],[f74,f64])).

fof(f463,plain,(
    ! [X7] : ~ r2_hidden(sK4,X7) ),
    inference(subsumption_resolution,[],[f459,f283])).

fof(f459,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK4,X7)
      | r2_hidden(sK5,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) ) ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK4,X7)
      | r2_hidden(sK5,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))
      | r2_hidden(sK5,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) ) ),
    inference(resolution,[],[f348,f111])).

fof(f348,plain,(
    ! [X0] :
      ( r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5))
      | ~ r2_hidden(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f343,f92])).

fof(f343,plain,(
    ! [X0] :
      ( r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5))
      | sK4 = k2_mcart_1(sK2)
      | ~ r2_hidden(sK4,X0) ) ),
    inference(resolution,[],[f210,f118])).

fof(f210,plain,
    ( r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))
    | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,
    ( r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))
    | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(resolution,[],[f161,f111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:23:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (17057)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (17058)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (17060)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (17065)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (17074)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (17058)Refutation not found, incomplete strategy% (17058)------------------------------
% 0.21/0.53  % (17058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17065)Refutation not found, incomplete strategy% (17065)------------------------------
% 0.21/0.53  % (17065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17058)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17058)Memory used [KB]: 10618
% 0.21/0.53  % (17058)Time elapsed: 0.113 s
% 0.21/0.53  % (17058)------------------------------
% 0.21/0.53  % (17058)------------------------------
% 0.21/0.53  % (17066)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (17065)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17065)Memory used [KB]: 10618
% 0.21/0.53  % (17065)Time elapsed: 0.122 s
% 0.21/0.53  % (17065)------------------------------
% 0.21/0.53  % (17065)------------------------------
% 0.21/0.53  % (17067)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (17066)Refutation not found, incomplete strategy% (17066)------------------------------
% 0.21/0.53  % (17066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17066)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.54  % (17066)Memory used [KB]: 10618
% 0.21/0.54  % (17066)Time elapsed: 0.107 s
% 0.21/0.54  % (17066)------------------------------
% 0.21/0.54  % (17066)------------------------------
% 0.21/0.54  % (17073)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (17073)Refutation not found, incomplete strategy% (17073)------------------------------
% 0.21/0.54  % (17073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17073)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17073)Memory used [KB]: 10618
% 0.21/0.54  % (17073)Time elapsed: 0.116 s
% 0.21/0.54  % (17073)------------------------------
% 0.21/0.54  % (17073)------------------------------
% 0.21/0.54  % (17080)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (17059)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (17056)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (17056)Refutation not found, incomplete strategy% (17056)------------------------------
% 0.21/0.54  % (17056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17056)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17056)Memory used [KB]: 1663
% 0.21/0.54  % (17056)Time elapsed: 0.126 s
% 0.21/0.54  % (17056)------------------------------
% 0.21/0.54  % (17056)------------------------------
% 0.21/0.54  % (17084)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (17064)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (17079)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (17075)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (17064)Refutation not found, incomplete strategy% (17064)------------------------------
% 0.21/0.55  % (17064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17064)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17064)Memory used [KB]: 10618
% 0.21/0.55  % (17064)Time elapsed: 0.110 s
% 0.21/0.55  % (17064)------------------------------
% 0.21/0.55  % (17064)------------------------------
% 0.21/0.55  % (17072)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (17062)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (17076)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (17077)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (17068)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (17071)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (17069)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (17078)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (17078)Refutation not found, incomplete strategy% (17078)------------------------------
% 0.21/0.56  % (17078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17078)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17078)Memory used [KB]: 10746
% 0.21/0.56  % (17078)Time elapsed: 0.119 s
% 0.21/0.56  % (17078)------------------------------
% 0.21/0.56  % (17078)------------------------------
% 0.21/0.56  % (17083)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (17082)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.55/0.57  % (17085)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.55/0.57  % (17063)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.57  % (17070)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.55/0.58  % (17081)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.68/0.58  % (17061)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.68/0.60  % (17085)Refutation found. Thanks to Tanya!
% 1.68/0.60  % SZS status Theorem for theBenchmark
% 1.68/0.60  % SZS output start Proof for theBenchmark
% 1.68/0.60  fof(f513,plain,(
% 1.68/0.60    $false),
% 1.68/0.60    inference(resolution,[],[f463,f375])).
% 1.68/0.60  fof(f375,plain,(
% 1.68/0.60    r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))),
% 1.68/0.60    inference(subsumption_resolution,[],[f374,f283])).
% 1.68/0.60  fof(f283,plain,(
% 1.68/0.60    ( ! [X0] : (~r2_hidden(sK5,X0)) )),
% 1.68/0.60    inference(resolution,[],[f266,f82])).
% 1.68/0.60  fof(f82,plain,(
% 1.68/0.60    r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK4,sK4,sK4,sK5))),
% 1.68/0.60    inference(resolution,[],[f58,f38])).
% 1.68/0.60  fof(f38,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f12])).
% 1.68/0.60  fof(f12,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.68/0.60    inference(ennf_transformation,[],[f7])).
% 1.68/0.60  fof(f7,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.68/0.60  fof(f58,plain,(
% 1.68/0.60    r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)))),
% 1.68/0.60    inference(definition_unfolding,[],[f31,f57,f56])).
% 1.68/0.60  fof(f56,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f35,f36])).
% 1.68/0.60  fof(f36,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f4])).
% 1.68/0.60  fof(f4,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.68/0.60  fof(f35,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f3])).
% 1.68/0.60  fof(f3,axiom,(
% 1.68/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.60  fof(f57,plain,(
% 1.68/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f34,f56])).
% 1.68/0.60  fof(f34,plain,(
% 1.68/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f2])).
% 1.68/0.60  fof(f2,axiom,(
% 1.68/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.60  fof(f31,plain,(
% 1.68/0.60    r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5)))),
% 1.68/0.60    inference(cnf_transformation,[],[f18])).
% 1.68/0.60  fof(f18,plain,(
% 1.68/0.60    ((sK5 != k2_mcart_1(sK2) & sK4 != k2_mcart_1(sK2)) | sK3 != k1_mcart_1(sK2)) & r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5)))),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f11,f17])).
% 1.68/0.60  fof(f17,plain,(
% 1.68/0.60    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))) => (((sK5 != k2_mcart_1(sK2) & sK4 != k2_mcart_1(sK2)) | sK3 != k1_mcart_1(sK2)) & r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f11,plain,(
% 1.68/0.60    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))))),
% 1.68/0.60    inference(ennf_transformation,[],[f10])).
% 1.68/0.60  fof(f10,negated_conjecture,(
% 1.68/0.60    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 1.68/0.60    inference(negated_conjecture,[],[f9])).
% 1.68/0.60  fof(f9,conjecture,(
% 1.68/0.60    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).
% 1.68/0.60  fof(f266,plain,(
% 1.68/0.60    ( ! [X0,X1] : (~r2_hidden(k2_mcart_1(sK2),X1) | ~r2_hidden(sK5,X0)) )),
% 1.68/0.60    inference(subsumption_resolution,[],[f263,f92])).
% 1.68/0.60  fof(f92,plain,(
% 1.68/0.60    sK4 != k2_mcart_1(sK2)),
% 1.68/0.60    inference(trivial_inequality_removal,[],[f91])).
% 1.68/0.60  fof(f91,plain,(
% 1.68/0.60    sK3 != sK3 | sK4 != k2_mcart_1(sK2)),
% 1.68/0.60    inference(backward_demodulation,[],[f32,f84])).
% 1.68/0.60  fof(f84,plain,(
% 1.68/0.60    sK3 = k1_mcart_1(sK2)),
% 1.68/0.60    inference(resolution,[],[f60,f58])).
% 1.68/0.60  fof(f60,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.68/0.60    inference(definition_unfolding,[],[f39,f57])).
% 1.68/0.60  fof(f39,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f13])).
% 1.68/0.60  fof(f13,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.68/0.60    inference(ennf_transformation,[],[f8])).
% 1.68/0.60  fof(f8,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.68/0.60  fof(f32,plain,(
% 1.68/0.60    sK4 != k2_mcart_1(sK2) | sK3 != k1_mcart_1(sK2)),
% 1.68/0.60    inference(cnf_transformation,[],[f18])).
% 1.68/0.60  fof(f263,plain,(
% 1.68/0.60    ( ! [X0,X1] : (~r2_hidden(sK5,X0) | sK4 = k2_mcart_1(sK2) | ~r2_hidden(k2_mcart_1(sK2),X1)) )),
% 1.68/0.60    inference(resolution,[],[f221,f118])).
% 1.68/0.60  fof(f118,plain,(
% 1.68/0.60    ( ! [X4,X2,X3] : (~r2_hidden(X2,k2_enumset1(X4,X4,X4,X4)) | X2 = X4 | ~r2_hidden(X2,X3)) )),
% 1.68/0.60    inference(resolution,[],[f87,f46])).
% 1.68/0.60  fof(f46,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f25])).
% 1.68/0.60  fof(f25,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.68/0.60    inference(rectify,[],[f24])).
% 1.68/0.60  fof(f24,plain,(
% 1.68/0.60    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.68/0.60    inference(flattening,[],[f23])).
% 1.68/0.60  fof(f23,plain,(
% 1.68/0.60    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.68/0.60    inference(nnf_transformation,[],[f14])).
% 1.68/0.60  fof(f14,plain,(
% 1.68/0.60    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.68/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.68/0.60  fof(f87,plain,(
% 1.68/0.60    ( ! [X6,X7,X5] : (sP0(k2_enumset1(X6,X6,X6,X6),X5,X7) | ~r2_hidden(X5,X7) | X5 = X6) )),
% 1.68/0.60    inference(resolution,[],[f61,f74])).
% 1.68/0.60  fof(f74,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 1.68/0.60    inference(resolution,[],[f41,f67])).
% 1.68/0.60  fof(f67,plain,(
% 1.68/0.60    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(equality_resolution,[],[f48])).
% 1.68/0.60  fof(f48,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.68/0.60    inference(cnf_transformation,[],[f26])).
% 1.68/0.60  fof(f26,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.68/0.60    inference(nnf_transformation,[],[f16])).
% 1.68/0.60  fof(f16,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.68/0.60    inference(definition_folding,[],[f1,f15,f14])).
% 1.68/0.60  fof(f15,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.68/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.68/0.60  fof(f1,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.68/0.60  fof(f41,plain,(
% 1.68/0.60    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f22])).
% 1.68/0.60  fof(f22,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).
% 1.68/0.60  fof(f21,plain,(
% 1.68/0.60    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f20,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.68/0.60    inference(rectify,[],[f19])).
% 1.68/0.60  fof(f19,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.68/0.60    inference(nnf_transformation,[],[f15])).
% 1.68/0.60  fof(f61,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f52,f57])).
% 1.68/0.60  fof(f52,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f28])).
% 1.68/0.60  fof(f28,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.68/0.60    inference(flattening,[],[f27])).
% 1.68/0.60  fof(f27,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.68/0.60    inference(nnf_transformation,[],[f5])).
% 1.68/0.60  fof(f5,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.68/0.60  fof(f221,plain,(
% 1.68/0.60    ( ! [X2] : (r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK4,sK4,sK4,sK4)) | ~r2_hidden(sK5,X2)) )),
% 1.68/0.60    inference(duplicate_literal_removal,[],[f220])).
% 1.68/0.60  fof(f220,plain,(
% 1.68/0.60    ( ! [X2] : (~r2_hidden(sK5,X2) | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK4,sK4,sK4,sK4)) | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK4,sK4,sK4,sK4))) )),
% 1.68/0.60    inference(resolution,[],[f211,f111])).
% 1.68/0.60  fof(f111,plain,(
% 1.68/0.60    ( ! [X30,X31,X29] : (~r2_hidden(X31,k2_enumset1(X29,X29,X29,X30)) | r2_hidden(X30,k2_enumset1(X31,X31,X31,X31)) | r2_hidden(X29,k2_enumset1(X31,X31,X31,X31))) )),
% 1.68/0.60    inference(superposition,[],[f68,f64])).
% 1.68/0.60  fof(f64,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f55,f56,f56])).
% 1.68/0.60  fof(f55,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f30])).
% 1.68/0.60  fof(f30,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.68/0.60    inference(flattening,[],[f29])).
% 1.68/0.60  fof(f29,plain,(
% 1.68/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.68/0.60    inference(nnf_transformation,[],[f6])).
% 1.68/0.60  fof(f6,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.68/0.60  fof(f68,plain,(
% 1.68/0.60    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 1.68/0.60    inference(equality_resolution,[],[f62])).
% 1.68/0.60  fof(f62,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 1.68/0.60    inference(definition_unfolding,[],[f51,f57])).
% 1.68/0.60  fof(f51,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f28])).
% 1.68/0.60  fof(f211,plain,(
% 1.68/0.60    ( ! [X0] : (r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) | ~r2_hidden(sK5,X0)) )),
% 1.68/0.60    inference(subsumption_resolution,[],[f208,f93])).
% 1.68/0.60  fof(f93,plain,(
% 1.68/0.60    sK5 != k2_mcart_1(sK2)),
% 1.68/0.60    inference(trivial_inequality_removal,[],[f90])).
% 1.68/0.60  fof(f90,plain,(
% 1.68/0.60    sK3 != sK3 | sK5 != k2_mcart_1(sK2)),
% 1.68/0.60    inference(backward_demodulation,[],[f33,f84])).
% 1.68/0.60  fof(f33,plain,(
% 1.68/0.60    sK5 != k2_mcart_1(sK2) | sK3 != k1_mcart_1(sK2)),
% 1.68/0.60    inference(cnf_transformation,[],[f18])).
% 1.68/0.60  fof(f208,plain,(
% 1.68/0.60    ( ! [X0] : (r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) | sK5 = k2_mcart_1(sK2) | ~r2_hidden(sK5,X0)) )),
% 1.68/0.60    inference(resolution,[],[f161,f118])).
% 1.68/0.60  fof(f161,plain,(
% 1.68/0.60    r2_hidden(sK5,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) | r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))),
% 1.68/0.60    inference(resolution,[],[f111,f82])).
% 1.68/0.60  fof(f374,plain,(
% 1.68/0.60    r2_hidden(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))),
% 1.68/0.60    inference(resolution,[],[f359,f111])).
% 1.68/0.60  fof(f359,plain,(
% 1.68/0.60    r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5))),
% 1.68/0.60    inference(resolution,[],[f342,f82])).
% 1.68/0.60  fof(f342,plain,(
% 1.68/0.60    ( ! [X19] : (~r2_hidden(k2_mcart_1(sK2),X19) | r2_hidden(sK4,X19)) )),
% 1.68/0.60    inference(subsumption_resolution,[],[f324,f283])).
% 1.68/0.60  fof(f324,plain,(
% 1.68/0.60    ( ! [X19] : (r2_hidden(sK5,X19) | r2_hidden(sK4,X19) | ~r2_hidden(k2_mcart_1(sK2),X19)) )),
% 1.68/0.60    inference(resolution,[],[f186,f82])).
% 1.68/0.60  fof(f186,plain,(
% 1.68/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | r2_hidden(X2,X3) | r2_hidden(X1,X3) | ~r2_hidden(X0,X3)) )),
% 1.68/0.60    inference(resolution,[],[f106,f46])).
% 1.68/0.60  fof(f106,plain,(
% 1.68/0.60    ( ! [X12,X10,X13,X11] : (sP0(X12,X13,k2_enumset1(X10,X10,X10,X11)) | ~r2_hidden(X13,k2_enumset1(X10,X10,X10,X11)) | r2_hidden(X11,X12) | r2_hidden(X10,X12)) )),
% 1.68/0.60    inference(superposition,[],[f74,f64])).
% 1.68/0.60  fof(f463,plain,(
% 1.68/0.60    ( ! [X7] : (~r2_hidden(sK4,X7)) )),
% 1.68/0.60    inference(subsumption_resolution,[],[f459,f283])).
% 1.68/0.60  fof(f459,plain,(
% 1.68/0.60    ( ! [X7] : (~r2_hidden(sK4,X7) | r2_hidden(sK5,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))) )),
% 1.68/0.60    inference(duplicate_literal_removal,[],[f458])).
% 1.68/0.60  fof(f458,plain,(
% 1.68/0.60    ( ! [X7] : (~r2_hidden(sK4,X7) | r2_hidden(sK5,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) | r2_hidden(sK5,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2)))) )),
% 1.68/0.60    inference(resolution,[],[f348,f111])).
% 1.68/0.60  fof(f348,plain,(
% 1.68/0.60    ( ! [X0] : (r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5)) | ~r2_hidden(sK4,X0)) )),
% 1.68/0.60    inference(subsumption_resolution,[],[f343,f92])).
% 1.68/0.60  fof(f343,plain,(
% 1.68/0.60    ( ! [X0] : (r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5)) | sK4 = k2_mcart_1(sK2) | ~r2_hidden(sK4,X0)) )),
% 1.68/0.60    inference(resolution,[],[f210,f118])).
% 1.68/0.60  fof(f210,plain,(
% 1.68/0.60    r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5))),
% 1.68/0.60    inference(duplicate_literal_removal,[],[f209])).
% 1.68/0.60  fof(f209,plain,(
% 1.68/0.60    r2_hidden(sK4,k2_enumset1(k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2),k2_mcart_1(sK2))) | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5)) | r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK5))),
% 1.68/0.60    inference(resolution,[],[f161,f111])).
% 1.68/0.60  % SZS output end Proof for theBenchmark
% 1.68/0.60  % (17085)------------------------------
% 1.68/0.60  % (17085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (17085)Termination reason: Refutation
% 1.68/0.60  
% 1.68/0.60  % (17085)Memory used [KB]: 2046
% 1.68/0.60  % (17085)Time elapsed: 0.154 s
% 1.68/0.60  % (17085)------------------------------
% 1.68/0.60  % (17085)------------------------------
% 1.68/0.60  % (17055)Success in time 0.232 s
%------------------------------------------------------------------------------
