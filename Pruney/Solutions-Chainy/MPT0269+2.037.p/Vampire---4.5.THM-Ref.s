%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 721 expanded)
%              Number of leaves         :    8 ( 185 expanded)
%              Depth                    :   30
%              Number of atoms          :  258 (4208 expanded)
%              Number of equality atoms :  120 (1396 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(subsumption_resolution,[],[f239,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f239,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f238,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f238,plain,(
    ! [X1] : sK0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f237,f187])).

fof(f187,plain,(
    ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f184,f36])).

fof(f36,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f20,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f184,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f183,f43])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f183,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f182,f35])).

fof(f35,plain,(
    sK0 != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f22,f34])).

fof(f22,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f182,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( sK1 != sK1
    | sK0 = k2_tarski(sK1,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f37,f174])).

fof(f174,plain,(
    sK1 = sK3(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( sK0 != sK0
    | sK1 = sK3(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( sK0 != sK0
    | sK1 = sK3(sK1,sK0)
    | sK1 = sK3(sK1,sK0) ),
    inference(superposition,[],[f35,f148])).

fof(f148,plain,(
    ! [X12] :
      ( sK3(X12,sK0) = X12
      | sK0 = k2_tarski(X12,X12)
      | sK1 = sK3(X12,sK0) ) ),
    inference(global_subsumption,[],[f147])).

fof(f147,plain,(
    ! [X8] :
      ( sK1 = sK3(X8,sK0)
      | sK3(X8,sK0) = X8
      | sK0 = k2_tarski(X8,X8) ) ),
    inference(resolution,[],[f140,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) = X0
      | k2_tarski(X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f140,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK0)
      | sK1 = X6 ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X6] :
      ( sK1 = X6
      | sK1 = X6
      | ~ r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f107,f74])).

fof(f74,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_xboole_0)
      | sK1 = X6
      | ~ r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f68,f41])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK0,k1_xboole_0))
      | sK1 = X0 ) ),
    inference(factoring,[],[f54])).

fof(f54,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k4_xboole_0(X10,k1_xboole_0))
      | ~ r2_hidden(X9,k4_xboole_0(sK0,X11))
      | sK1 = X9 ) ),
    inference(resolution,[],[f49,f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0))
      | sK1 = X0 ) ),
    inference(resolution,[],[f48,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_tarski(sK1,sK1))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f47,f42])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,k2_tarski(sK1,sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f41,f36])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | sK1 = X0 ) ),
    inference(superposition,[],[f99,f36])).

fof(f99,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,k4_xboole_0(sK0,X12))
      | sK1 = X11 ) ),
    inference(subsumption_resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,k4_xboole_0(sK0,X12))
      | sK1 = X11
      | r2_hidden(X11,k2_tarski(sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f93,f43])).

fof(f93,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,k4_xboole_0(sK0,X12))
      | sK1 = X11
      | r2_hidden(X11,k2_tarski(sK1,sK1))
      | ~ r2_hidden(X11,sK0) ) ),
    inference(resolution,[],[f69,f47])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k4_xboole_0(sK0,X1))
      | sK1 = X0 ) ),
    inference(superposition,[],[f54,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | k2_tarski(X0,X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f237,plain,(
    ! [X1] :
      ( r2_hidden(sK1,k1_xboole_0)
      | sK0 = k4_xboole_0(k1_xboole_0,X1) ) ),
    inference(subsumption_resolution,[],[f234,f183])).

fof(f234,plain,(
    ! [X1] :
      ( r2_hidden(sK1,sK0)
      | r2_hidden(sK1,k1_xboole_0)
      | sK0 = k4_xboole_0(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f26,f230])).

fof(f230,plain,(
    ! [X29] : sK1 = sK2(k1_xboole_0,X29,sK0) ),
    inference(subsumption_resolution,[],[f229,f21])).

fof(f229,plain,(
    ! [X29] :
      ( k1_xboole_0 = sK0
      | sK1 = sK2(k1_xboole_0,X29,sK0) ) ),
    inference(forward_demodulation,[],[f221,f33])).

fof(f221,plain,(
    ! [X29] :
      ( sK1 = sK2(k1_xboole_0,X29,sK0)
      | sK0 = k4_xboole_0(k1_xboole_0,X29) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X29] :
      ( sK1 = sK2(k1_xboole_0,X29,sK0)
      | sK0 = k4_xboole_0(k1_xboole_0,X29)
      | sK1 = sK2(k1_xboole_0,X29,sK0) ) ),
    inference(resolution,[],[f188,f107])).

fof(f188,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,sK0),X3)
      | sK1 = sK2(X3,X4,sK0)
      | sK0 = k4_xboole_0(X3,X4) ) ),
    inference(global_subsumption,[],[f144])).

fof(f144,plain,(
    ! [X2,X3] :
      ( sK1 = sK2(X2,X3,sK0)
      | r2_hidden(sK2(X2,X3,sK0),X2)
      | sK0 = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f140,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (3097)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.51  % (3088)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (3079)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (3076)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (3074)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (3085)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (3086)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (3075)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (3085)Refutation not found, incomplete strategy% (3085)------------------------------
% 0.22/0.52  % (3085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3073)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (3085)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3085)Memory used [KB]: 10618
% 0.22/0.52  % (3085)Time elapsed: 0.108 s
% 0.22/0.52  % (3085)------------------------------
% 0.22/0.52  % (3085)------------------------------
% 0.22/0.53  % (3077)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (3089)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (3072)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (3101)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (3078)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (3091)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (3084)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (3093)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (3083)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (3081)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (3090)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (3094)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (3083)Refutation not found, incomplete strategy% (3083)------------------------------
% 0.22/0.54  % (3083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3083)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (3083)Memory used [KB]: 10746
% 0.22/0.54  % (3083)Time elapsed: 0.130 s
% 0.22/0.54  % (3083)------------------------------
% 0.22/0.54  % (3083)------------------------------
% 0.22/0.54  % (3092)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (3073)Refutation not found, incomplete strategy% (3073)------------------------------
% 0.22/0.54  % (3073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3073)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (3073)Memory used [KB]: 1663
% 0.22/0.54  % (3073)Time elapsed: 0.125 s
% 0.22/0.54  % (3073)------------------------------
% 0.22/0.54  % (3073)------------------------------
% 0.22/0.54  % (3097)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f239,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f6])).
% 0.22/0.54  fof(f6,conjecture,(
% 0.22/0.54    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    k1_xboole_0 = sK0),
% 0.22/0.54    inference(forward_demodulation,[],[f238,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    ( ! [X1] : (sK0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f237,f187])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.54    inference(superposition,[],[f184,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1))),
% 0.22/0.54    inference(definition_unfolding,[],[f20,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(sK0,X0))) )),
% 0.22/0.54    inference(resolution,[],[f183,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f182,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    sK0 != k2_tarski(sK1,sK1)),
% 0.22/0.54    inference(definition_unfolding,[],[f22,f34])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    sK0 != k1_tarski(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    sK0 = k2_tarski(sK1,sK1) | ~r2_hidden(sK1,sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f181])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    sK1 != sK1 | sK0 = k2_tarski(sK1,sK1) | ~r2_hidden(sK1,sK0)),
% 0.22/0.54    inference(superposition,[],[f37,f174])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    sK1 = sK3(sK1,sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    sK0 != sK0 | sK1 = sK3(sK1,sK0)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f166])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    sK0 != sK0 | sK1 = sK3(sK1,sK0) | sK1 = sK3(sK1,sK0)),
% 0.22/0.54    inference(superposition,[],[f35,f148])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    ( ! [X12] : (sK3(X12,sK0) = X12 | sK0 = k2_tarski(X12,X12) | sK1 = sK3(X12,sK0)) )),
% 0.22/0.54    inference(global_subsumption,[],[f147])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X8] : (sK1 = sK3(X8,sK0) | sK3(X8,sK0) = X8 | sK0 = k2_tarski(X8,X8)) )),
% 0.22/0.54    inference(resolution,[],[f140,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) = X0 | k2_tarski(X0,X0) = X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f34])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    ( ! [X6] : (~r2_hidden(X6,sK0) | sK1 = X6) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    ( ! [X6] : (sK1 = X6 | sK1 = X6 | ~r2_hidden(X6,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f107,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X6] : (r2_hidden(X6,k1_xboole_0) | sK1 = X6 | ~r2_hidden(X6,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f68,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k1_xboole_0)) | sK1 = X0) )),
% 0.22/0.54    inference(factoring,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X10,X11,X9] : (~r2_hidden(X9,k4_xboole_0(X10,k1_xboole_0)) | ~r2_hidden(X9,k4_xboole_0(sK0,X11)) | sK1 = X9) )),
% 0.22/0.54    inference(resolution,[],[f49,f43])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0)) | sK1 = X0) )),
% 0.22/0.54    inference(resolution,[],[f48,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f34])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(sK1,sK1)) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0))) )),
% 0.22/0.54    inference(resolution,[],[f47,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k2_tarski(sK1,sK1)) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.54    inference(superposition,[],[f41,f36])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK1 = X0) )),
% 0.22/0.54    inference(superposition,[],[f99,f36])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X12,X11] : (~r2_hidden(X11,k4_xboole_0(sK0,X12)) | sK1 = X11) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f98,f46])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X12,X11] : (~r2_hidden(X11,k4_xboole_0(sK0,X12)) | sK1 = X11 | r2_hidden(X11,k2_tarski(sK1,sK1))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f93,f43])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X12,X11] : (~r2_hidden(X11,k4_xboole_0(sK0,X12)) | sK1 = X11 | r2_hidden(X11,k2_tarski(sK1,sK1)) | ~r2_hidden(X11,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f69,f47])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k4_xboole_0(sK0,X1)) | sK1 = X0) )),
% 0.22/0.54    inference(superposition,[],[f54,f33])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK3(X0,X1) != X0 | k2_tarski(X0,X0) = X1 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f32,f34])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(sK1,k1_xboole_0) | sK0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f234,f183])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(sK1,sK0) | r2_hidden(sK1,k1_xboole_0) | sK0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(superposition,[],[f26,f230])).
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    ( ! [X29] : (sK1 = sK2(k1_xboole_0,X29,sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f229,f21])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    ( ! [X29] : (k1_xboole_0 = sK0 | sK1 = sK2(k1_xboole_0,X29,sK0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f221,f33])).
% 0.22/0.54  fof(f221,plain,(
% 0.22/0.54    ( ! [X29] : (sK1 = sK2(k1_xboole_0,X29,sK0) | sK0 = k4_xboole_0(k1_xboole_0,X29)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f212])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    ( ! [X29] : (sK1 = sK2(k1_xboole_0,X29,sK0) | sK0 = k4_xboole_0(k1_xboole_0,X29) | sK1 = sK2(k1_xboole_0,X29,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f188,f107])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,sK0),X3) | sK1 = sK2(X3,X4,sK0) | sK0 = k4_xboole_0(X3,X4)) )),
% 0.22/0.54    inference(global_subsumption,[],[f144])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X2,X3] : (sK1 = sK2(X2,X3,sK0) | r2_hidden(sK2(X2,X3,sK0),X2) | sK0 = k4_xboole_0(X2,X3)) )),
% 0.22/0.54    inference(resolution,[],[f140,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (3097)------------------------------
% 0.22/0.54  % (3097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3097)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (3097)Memory used [KB]: 10874
% 0.22/0.54  % (3097)Time elapsed: 0.073 s
% 0.22/0.54  % (3097)------------------------------
% 0.22/0.54  % (3097)------------------------------
% 0.22/0.54  % (3089)Refutation not found, incomplete strategy% (3089)------------------------------
% 0.22/0.54  % (3089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3089)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (3089)Memory used [KB]: 10618
% 0.22/0.54  % (3089)Time elapsed: 0.136 s
% 0.22/0.54  % (3089)------------------------------
% 0.22/0.54  % (3089)------------------------------
% 0.22/0.55  % (3069)Success in time 0.179 s
%------------------------------------------------------------------------------
