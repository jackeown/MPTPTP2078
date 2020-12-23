%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:53 EST 2020

% Result     : Theorem 19.85s
% Output     : Refutation 19.85s
% Verified   : 
% Statistics : Number of formulae       :  183 (58433 expanded)
%              Number of leaves         :    9 (17141 expanded)
%              Depth                    :   44
%              Number of atoms          :  280 (223888 expanded)
%              Number of equality atoms :  173 (61145 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f100921])).

fof(f100921,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f100920])).

fof(f100920,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f32,f100919])).

fof(f100919,plain,(
    ! [X225,X223,X224] : k4_xboole_0(k2_xboole_0(X224,X225),X223) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,X223)) ),
    inference(forward_demodulation,[],[f100918,f104])).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f20,f47])).

fof(f47,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    inference(forward_demodulation,[],[f43,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f19,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f43,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f34,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f100918,plain,(
    ! [X225,X223,X224] : k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k4_xboole_0(k2_xboole_0(X224,X225),X223) ),
    inference(forward_demodulation,[],[f100917,f54962])).

fof(f54962,plain,(
    ! [X269,X267,X268] : k4_xboole_0(k2_xboole_0(X268,X269),X267) = k4_xboole_0(k2_xboole_0(X269,k2_xboole_0(X267,X268)),X267) ),
    inference(superposition,[],[f34,f45592])).

fof(f45592,plain,(
    ! [X45,X43,X44] : k2_xboole_0(X45,k2_xboole_0(X43,X44)) = k2_xboole_0(X44,k2_xboole_0(X45,X43)) ),
    inference(forward_demodulation,[],[f45591,f3332])).

fof(f3332,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f3286,f3199])).

fof(f3199,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,X10)) = X9 ),
    inference(resolution,[],[f3094,f1053])).

fof(f1053,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(X3,X4,X3),X4)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(global_subsumption,[],[f283,f1051])).

fof(f1051,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(X3,X4,X3),X4)
      | ~ r2_hidden(sK3(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(duplicate_literal_removal,[],[f1047])).

fof(f1047,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(X3,X4,X3),X4)
      | ~ r2_hidden(sK3(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f26,f283])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f283,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3094,plain,(
    ! [X10,X11] : ~ r2_hidden(X11,k4_xboole_0(X10,X10)) ),
    inference(superposition,[],[f3011,f104])).

fof(f3011,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f2977,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f48,f17])).

fof(f48,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f44,f18])).

fof(f44,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f18,f34])).

fof(f2977,plain,(
    ! [X39,X41,X42,X40] : ~ r2_hidden(X41,k4_xboole_0(X39,k2_xboole_0(X39,k2_xboole_0(X40,X42)))) ),
    inference(subsumption_resolution,[],[f2916,f2970])).

fof(f2970,plain,(
    ! [X39,X37,X41,X38,X40] :
      ( ~ r2_hidden(X37,k4_xboole_0(X38,k2_xboole_0(X39,X38)))
      | ~ r2_hidden(X37,k4_xboole_0(X40,k2_xboole_0(X39,X41))) ) ),
    inference(resolution,[],[f2837,f758])).

fof(f758,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r2_hidden(X12,X14)
      | ~ r2_hidden(X12,k4_xboole_0(X13,k2_xboole_0(X14,X15))) ) ),
    inference(resolution,[],[f108,f28])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f108,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(X11,k4_xboole_0(X8,X9))
      | ~ r2_hidden(X11,k4_xboole_0(X8,k2_xboole_0(X9,X10))) ) ),
    inference(superposition,[],[f29,f20])).

fof(f29,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2837,plain,(
    ! [X24,X23,X22] :
      ( r2_hidden(X24,X22)
      | ~ r2_hidden(X24,k4_xboole_0(X23,k2_xboole_0(X22,X23))) ) ),
    inference(superposition,[],[f29,f2712])).

fof(f2712,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X3,X4)) = k4_xboole_0(X4,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f1171,f111])).

fof(f111,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(X4,k2_xboole_0(X3,X5)) ),
    inference(forward_demodulation,[],[f101,f20])).

fof(f101,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(k4_xboole_0(X4,X3),X5) ),
    inference(superposition,[],[f20,f34])).

fof(f1171,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f110,f17])).

fof(f110,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f100,f20])).

fof(f100,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f20,f19])).

fof(f2916,plain,(
    ! [X39,X41,X42,X40] :
      ( ~ r2_hidden(X41,k4_xboole_0(X39,k2_xboole_0(X39,k2_xboole_0(X40,X42))))
      | r2_hidden(X41,k4_xboole_0(X40,k2_xboole_0(X39,X40))) ) ),
    inference(forward_demodulation,[],[f2844,f114])).

fof(f114,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) = k4_xboole_0(X9,k2_xboole_0(X10,k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f113,f20])).

fof(f113,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) ),
    inference(forward_demodulation,[],[f103,f20])).

fof(f103,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X12) ),
    inference(superposition,[],[f20,f20])).

fof(f2844,plain,(
    ! [X39,X41,X42,X40] :
      ( r2_hidden(X41,k4_xboole_0(X40,k2_xboole_0(X39,X40)))
      | ~ r2_hidden(X41,k4_xboole_0(X39,k2_xboole_0(k2_xboole_0(X39,X40),X42))) ) ),
    inference(superposition,[],[f108,f2712])).

fof(f3286,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f3199,f36])).

fof(f36,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f19,f18])).

fof(f45591,plain,(
    ! [X45,X43,X44] : k2_xboole_0(X44,k2_xboole_0(X45,X43)) = k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) ),
    inference(forward_demodulation,[],[f45590,f45049])).

fof(f45049,plain,(
    ! [X45,X43,X44] : k2_xboole_0(X44,k2_xboole_0(X45,X43)) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X44,k2_xboole_0(X45,X43))) ),
    inference(forward_demodulation,[],[f45048,f48])).

fof(f45048,plain,(
    ! [X45,X43,X44] : k2_xboole_0(X44,k2_xboole_0(X44,k2_xboole_0(X45,X43))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X44,k2_xboole_0(X44,k2_xboole_0(X45,X43)))) ),
    inference(forward_demodulation,[],[f45047,f34636])).

fof(f34636,plain,(
    ! [X557,X559,X556,X558] : k2_xboole_0(k2_xboole_0(X559,X558),k2_xboole_0(X556,X557)) = k2_xboole_0(X558,k2_xboole_0(X559,k2_xboole_0(X557,X556))) ),
    inference(forward_demodulation,[],[f34250,f25344])).

fof(f25344,plain,(
    ! [X239,X237,X236] : k2_xboole_0(X237,k2_xboole_0(X236,X239)) = k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(X237,X236))) ),
    inference(forward_demodulation,[],[f25343,f3601])).

fof(f3601,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f3528,f34])).

fof(f3528,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(superposition,[],[f3335,f107])).

fof(f107,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f18,f20])).

fof(f3335,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X5)) = X4 ),
    inference(forward_demodulation,[],[f3289,f3199])).

fof(f3289,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X5)) = k4_xboole_0(X4,k4_xboole_0(X5,X5)) ),
    inference(superposition,[],[f3199,f19])).

fof(f25343,plain,(
    ! [X239,X237,X238,X236] : k2_xboole_0(X237,k2_xboole_0(X236,X239)) = k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(X237,k2_xboole_0(X236,k4_xboole_0(X236,X238))))) ),
    inference(forward_demodulation,[],[f25342,f16838])).

fof(f16838,plain,(
    ! [X173,X176,X174] : k2_xboole_0(X176,k2_xboole_0(X173,X174)) = k2_xboole_0(X176,k2_xboole_0(X174,X173)) ),
    inference(forward_demodulation,[],[f16693,f3334])).

fof(f3334,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X2),X3) = X3 ),
    inference(forward_demodulation,[],[f3288,f3199])).

fof(f3288,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X2),X3) = k4_xboole_0(X3,k4_xboole_0(X2,X2)) ),
    inference(superposition,[],[f3199,f34])).

fof(f16693,plain,(
    ! [X175,X173,X176,X174] : k2_xboole_0(k2_xboole_0(k4_xboole_0(X175,X175),X176),k2_xboole_0(X173,X174)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X175,X175),X176),k2_xboole_0(X174,X173)) ),
    inference(superposition,[],[f1232,f15295])).

fof(f15295,plain,(
    ! [X144,X142,X143] : k2_xboole_0(X142,X143) = k2_xboole_0(k2_xboole_0(X143,X142),k4_xboole_0(X144,X144)) ),
    inference(forward_demodulation,[],[f15045,f58])).

fof(f58,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f57,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f37,f18])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f19])).

fof(f57,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k2_xboole_0(X7,X6)) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f52,f17])).

fof(f52,plain,(
    ! [X6,X7] : k2_xboole_0(k2_xboole_0(X7,X6),X6) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f40,f40])).

fof(f15045,plain,(
    ! [X144,X142,X143] : k2_xboole_0(k2_xboole_0(X143,X142),k4_xboole_0(X144,X144)) = k2_xboole_0(k2_xboole_0(X143,X142),k2_xboole_0(X142,X143)) ),
    inference(superposition,[],[f1113,f3536])).

fof(f3536,plain,(
    ! [X28,X27] : k4_xboole_0(X27,X27) = k4_xboole_0(X28,X28) ),
    inference(superposition,[],[f3335,f3334])).

fof(f1113,plain,(
    ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X17,X16),k4_xboole_0(X18,k2_xboole_0(X16,X17))) = k2_xboole_0(k2_xboole_0(X17,X16),X18) ),
    inference(forward_demodulation,[],[f1076,f1112])).

fof(f1112,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k2_xboole_0(X14,X13),k4_xboole_0(X15,X13)) = k2_xboole_0(k2_xboole_0(X14,X13),X15) ),
    inference(forward_demodulation,[],[f1075,f18])).

fof(f1075,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k2_xboole_0(X14,X13),k4_xboole_0(X15,X13)) = k2_xboole_0(k2_xboole_0(X14,X13),k4_xboole_0(X15,k2_xboole_0(X14,X13))) ),
    inference(superposition,[],[f107,f65])).

fof(f1076,plain,(
    ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X17,X16),k4_xboole_0(X18,X16)) = k2_xboole_0(k2_xboole_0(X17,X16),k4_xboole_0(X18,k2_xboole_0(X16,X17))) ),
    inference(superposition,[],[f107,f40])).

fof(f1232,plain,(
    ! [X10,X11,X9] : k2_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(X10,X11),X9) ),
    inference(forward_demodulation,[],[f1197,f18])).

fof(f1197,plain,(
    ! [X10,X11,X9] : k2_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X9,k2_xboole_0(X10,X11))) ),
    inference(superposition,[],[f18,f110])).

fof(f25342,plain,(
    ! [X239,X237,X238,X236] : k2_xboole_0(X237,k2_xboole_0(X236,X239)) = k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(X237,k2_xboole_0(k4_xboole_0(X236,X238),X236)))) ),
    inference(forward_demodulation,[],[f25341,f114])).

fof(f25341,plain,(
    ! [X239,X237,X238,X236] : k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(k2_xboole_0(X237,k4_xboole_0(X236,X238)),X236))) = k2_xboole_0(X237,k2_xboole_0(X236,X239)) ),
    inference(forward_demodulation,[],[f25147,f21992])).

fof(f21992,plain,(
    ! [X14,X12,X13] : k2_xboole_0(X13,k2_xboole_0(X12,X14)) = k2_xboole_0(k2_xboole_0(X12,X13),X14) ),
    inference(forward_demodulation,[],[f21991,f21396])).

fof(f21396,plain,(
    ! [X24,X23] : k2_xboole_0(X24,X23) = k2_xboole_0(k4_xboole_0(X24,X23),X23) ),
    inference(forward_demodulation,[],[f21236,f5842])).

fof(f5842,plain,(
    ! [X80,X78,X79] : k2_xboole_0(X78,X79) = k4_xboole_0(k2_xboole_0(X79,X78),k4_xboole_0(X80,X80)) ),
    inference(forward_demodulation,[],[f5841,f3199])).

fof(f5841,plain,(
    ! [X80,X78,X79] : k4_xboole_0(k2_xboole_0(X79,X78),k4_xboole_0(X80,X80)) = k4_xboole_0(k2_xboole_0(X78,X79),k4_xboole_0(X80,X80)) ),
    inference(forward_demodulation,[],[f5840,f40])).

fof(f5840,plain,(
    ! [X80,X78,X79] : k4_xboole_0(k2_xboole_0(X79,X78),k4_xboole_0(X80,X80)) = k4_xboole_0(k2_xboole_0(X78,k2_xboole_0(X79,X78)),k4_xboole_0(X80,X80)) ),
    inference(forward_demodulation,[],[f5793,f17])).

fof(f5793,plain,(
    ! [X80,X78,X79] : k4_xboole_0(k2_xboole_0(X79,X78),k4_xboole_0(X80,X80)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X79,X78),X78),k4_xboole_0(X80,X80)) ),
    inference(superposition,[],[f36,f3631])).

fof(f3631,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X6,X6) = k4_xboole_0(X5,k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f3536,f111])).

fof(f21236,plain,(
    ! [X24,X23,X25] : k2_xboole_0(k4_xboole_0(X24,X23),X23) = k4_xboole_0(k2_xboole_0(X23,X24),k4_xboole_0(X25,X25)) ),
    inference(superposition,[],[f5842,f18])).

fof(f21991,plain,(
    ! [X14,X12,X13] : k2_xboole_0(k4_xboole_0(X13,k2_xboole_0(X12,X14)),k2_xboole_0(X12,X14)) = k2_xboole_0(k2_xboole_0(X12,X13),X14) ),
    inference(forward_demodulation,[],[f21758,f1399])).

fof(f1399,plain,(
    ! [X14,X12,X13] : k2_xboole_0(k2_xboole_0(X12,X14),k2_xboole_0(X12,X13)) = k2_xboole_0(k2_xboole_0(X12,X14),X13) ),
    inference(forward_demodulation,[],[f1364,f18])).

fof(f1364,plain,(
    ! [X14,X12,X13] : k2_xboole_0(k2_xboole_0(X12,X14),k2_xboole_0(X12,X13)) = k2_xboole_0(k2_xboole_0(X12,X14),k4_xboole_0(X13,k2_xboole_0(X12,X14))) ),
    inference(superposition,[],[f18,f111])).

fof(f21758,plain,(
    ! [X14,X12,X13] : k2_xboole_0(k4_xboole_0(X13,k2_xboole_0(X12,X14)),k2_xboole_0(X12,X14)) = k2_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X12,X14)) ),
    inference(superposition,[],[f21396,f111])).

fof(f25147,plain,(
    ! [X239,X237,X238,X236] : k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(k2_xboole_0(X237,k4_xboole_0(X236,X238)),X236))) = k2_xboole_0(k2_xboole_0(X236,X237),X239) ),
    inference(superposition,[],[f1113,f7485])).

fof(f7485,plain,(
    ! [X101,X102,X100] : k2_xboole_0(X100,X102) = k2_xboole_0(X100,k2_xboole_0(X102,k4_xboole_0(X100,X101))) ),
    inference(superposition,[],[f1232,f3799])).

fof(f3799,plain,(
    ! [X33,X32] : k2_xboole_0(k4_xboole_0(X32,X33),X32) = X32 ),
    inference(superposition,[],[f65,f3601])).

fof(f34250,plain,(
    ! [X557,X559,X556,X558] : k2_xboole_0(k2_xboole_0(X559,X558),k2_xboole_0(X556,X557)) = k2_xboole_0(k2_xboole_0(X559,X558),k4_xboole_0(k2_xboole_0(X557,X556),k2_xboole_0(X558,X559))) ),
    inference(superposition,[],[f1113,f16652])).

fof(f16652,plain,(
    ! [X35,X33,X34] : k4_xboole_0(k2_xboole_0(X33,X34),X35) = k4_xboole_0(k2_xboole_0(X34,X33),X35) ),
    inference(superposition,[],[f3816,f15295])).

fof(f3816,plain,(
    ! [X83,X84,X82] : k4_xboole_0(X84,X82) = k4_xboole_0(k2_xboole_0(X84,k4_xboole_0(X82,X83)),X82) ),
    inference(superposition,[],[f1171,f3601])).

fof(f45047,plain,(
    ! [X45,X43,X44] : k2_xboole_0(k2_xboole_0(X44,X44),k2_xboole_0(X43,X45)) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(k2_xboole_0(X44,X44),k2_xboole_0(X43,X45))) ),
    inference(forward_demodulation,[],[f44682,f21992])).

fof(f44682,plain,(
    ! [X45,X43,X44] : k2_xboole_0(k2_xboole_0(X43,k2_xboole_0(X44,X44)),X45) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(k2_xboole_0(X43,k2_xboole_0(X44,X44)),X45)) ),
    inference(superposition,[],[f25547,f128])).

fof(f128,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1) ),
    inference(forward_demodulation,[],[f115,f104])).

fof(f115,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1) ),
    inference(superposition,[],[f104,f19])).

fof(f25547,plain,(
    ! [X50,X51,X49] : k2_xboole_0(X49,X50) = k2_xboole_0(k4_xboole_0(X49,X51),k2_xboole_0(X49,X50)) ),
    inference(superposition,[],[f7640,f17])).

fof(f7640,plain,(
    ! [X101,X102,X100] : k2_xboole_0(X100,X102) = k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X100,X101)) ),
    inference(forward_demodulation,[],[f7639,f48])).

fof(f7639,plain,(
    ! [X101,X102,X100] : k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X100,X101)) = k2_xboole_0(X100,k2_xboole_0(X100,X102)) ),
    inference(forward_demodulation,[],[f7509,f17])).

fof(f7509,plain,(
    ! [X101,X102,X100] : k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X100,X101)) = k2_xboole_0(k2_xboole_0(X100,X102),X100) ),
    inference(superposition,[],[f1232,f3799])).

fof(f45590,plain,(
    ! [X45,X43,X44] : k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X44,k2_xboole_0(X45,X43))) ),
    inference(forward_demodulation,[],[f45589,f48])).

fof(f45589,plain,(
    ! [X45,X43,X44] : k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X44,k2_xboole_0(X44,k2_xboole_0(X45,X43)))) ),
    inference(forward_demodulation,[],[f45588,f34636])).

fof(f45588,plain,(
    ! [X45,X43,X44] : k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(k2_xboole_0(X44,X44),k2_xboole_0(X43,X45))) ),
    inference(forward_demodulation,[],[f45202,f21992])).

fof(f45202,plain,(
    ! [X45,X43,X44] : k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(k2_xboole_0(X43,k2_xboole_0(X44,X44)),X45)) ),
    inference(superposition,[],[f25763,f128])).

fof(f25763,plain,(
    ! [X449,X448,X450] : k2_xboole_0(k4_xboole_0(X448,X450),k2_xboole_0(X448,X449)) = k2_xboole_0(X449,X448) ),
    inference(forward_demodulation,[],[f25651,f5842])).

fof(f25651,plain,(
    ! [X449,X451,X448,X450] : k2_xboole_0(k4_xboole_0(X448,X450),k2_xboole_0(X448,X449)) = k4_xboole_0(k2_xboole_0(X448,X449),k4_xboole_0(X451,X451)) ),
    inference(superposition,[],[f5842,f7640])).

fof(f100917,plain,(
    ! [X225,X223,X224] : k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k4_xboole_0(k2_xboole_0(X225,k2_xboole_0(X223,X224)),X223) ),
    inference(forward_demodulation,[],[f100916,f21992])).

fof(f100916,plain,(
    ! [X225,X223,X224] : k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X223,X225),X224),X223) ),
    inference(forward_demodulation,[],[f100915,f90531])).

fof(f90531,plain,(
    ! [X94,X92,X93] : k4_xboole_0(k2_xboole_0(X94,X93),X92) = k2_xboole_0(k4_xboole_0(X93,X92),k4_xboole_0(k2_xboole_0(X94,X93),X92)) ),
    inference(superposition,[],[f80102,f88779])).

fof(f88779,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X3,X2),X4))) = X4 ),
    inference(superposition,[],[f83225,f17])).

fof(f83225,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(k2_xboole_0(X6,X7),X8))) = X8 ),
    inference(forward_demodulation,[],[f82903,f13683])).

fof(f13683,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X25,k2_xboole_0(k4_xboole_0(X26,X25),X27)) = k4_xboole_0(X25,X27) ),
    inference(superposition,[],[f20,f13466])).

fof(f13466,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f13446,f3332])).

fof(f13446,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(duplicate_literal_removal,[],[f13351])).

fof(f13351,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0
      | k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ) ),
    inference(resolution,[],[f289,f1053])).

fof(f289,plain,(
    ! [X17,X15,X18,X16] :
      ( ~ r2_hidden(sK3(X15,X16,X15),k4_xboole_0(X17,k2_xboole_0(X18,X15)))
      | k4_xboole_0(X15,X16) = X15 ) ),
    inference(resolution,[],[f283,f109])).

fof(f109,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r2_hidden(X15,X14)
      | ~ r2_hidden(X15,k4_xboole_0(X12,k2_xboole_0(X13,X14))) ) ),
    inference(superposition,[],[f28,f20])).

fof(f82903,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(k2_xboole_0(X6,X7),X8)))) = X8 ),
    inference(superposition,[],[f78200,f956])).

fof(f956,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X3,X2),X4)) ),
    inference(forward_demodulation,[],[f920,f20])).

fof(f920,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,X2)),X4) ),
    inference(superposition,[],[f20,f36])).

fof(f78200,plain,(
    ! [X118,X116,X117] : k2_xboole_0(X118,k4_xboole_0(X116,k2_xboole_0(X117,k4_xboole_0(X116,X118)))) = X118 ),
    inference(forward_demodulation,[],[f78199,f107])).

fof(f78199,plain,(
    ! [X118,X116,X117] : k2_xboole_0(X118,k4_xboole_0(X116,k2_xboole_0(X117,k4_xboole_0(X116,k2_xboole_0(X118,X117))))) = X118 ),
    inference(forward_demodulation,[],[f77835,f20])).

fof(f77835,plain,(
    ! [X118,X116,X117] : k2_xboole_0(X118,k4_xboole_0(k4_xboole_0(X116,X117),k4_xboole_0(X116,k2_xboole_0(X118,X117)))) = X118 ),
    inference(superposition,[],[f77444,f16507])).

fof(f16507,plain,(
    ! [X233,X234,X232] : k4_xboole_0(k4_xboole_0(X233,X232),X234) = k4_xboole_0(X233,k2_xboole_0(X234,X232)) ),
    inference(forward_demodulation,[],[f16375,f2761])).

fof(f2761,plain,(
    ! [X76,X74,X75] : k4_xboole_0(k4_xboole_0(X74,X75),k2_xboole_0(X76,X75)) = k4_xboole_0(X74,k2_xboole_0(X76,X75)) ),
    inference(forward_demodulation,[],[f2686,f1338])).

fof(f1338,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f111,f17])).

fof(f2686,plain,(
    ! [X76,X74,X75] : k4_xboole_0(k4_xboole_0(X74,X75),k2_xboole_0(X76,X75)) = k4_xboole_0(k2_xboole_0(X75,X74),k2_xboole_0(X76,X75)) ),
    inference(superposition,[],[f1171,f955])).

fof(f955,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f954,f56])).

fof(f56,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f55,f18])).

fof(f55,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f51,f17])).

fof(f51,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f40,f18])).

fof(f954,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f919,f18])).

fof(f919,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f18,f36])).

fof(f16375,plain,(
    ! [X233,X234,X232] : k4_xboole_0(k4_xboole_0(X233,X232),X234) = k4_xboole_0(k4_xboole_0(X233,X232),k2_xboole_0(X234,X232)) ),
    inference(superposition,[],[f13724,f13466])).

fof(f13724,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) ),
    inference(forward_demodulation,[],[f13674,f1118])).

fof(f1118,plain,(
    ! [X57,X56,X55] : k2_xboole_0(X56,k4_xboole_0(X57,k4_xboole_0(X55,X56))) = k2_xboole_0(X56,k4_xboole_0(X57,X55)) ),
    inference(forward_demodulation,[],[f1083,f1071])).

fof(f1071,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f107,f17])).

fof(f1083,plain,(
    ! [X57,X56,X55] : k2_xboole_0(X56,k4_xboole_0(X57,k4_xboole_0(X55,X56))) = k2_xboole_0(X56,k4_xboole_0(X57,k2_xboole_0(X56,X55))) ),
    inference(superposition,[],[f107,f955])).

fof(f13674,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f13466,f20])).

fof(f77444,plain,(
    ! [X37,X36] : k2_xboole_0(X37,k4_xboole_0(X36,k4_xboole_0(X36,X37))) = X37 ),
    inference(forward_demodulation,[],[f77443,f3601])).

fof(f77443,plain,(
    ! [X37,X36] : k2_xboole_0(X37,k4_xboole_0(X37,X36)) = k2_xboole_0(X37,k4_xboole_0(X36,k4_xboole_0(X36,X37))) ),
    inference(forward_demodulation,[],[f77015,f1118])).

fof(f77015,plain,(
    ! [X37,X36] : k2_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X36,X37))) = k2_xboole_0(X37,k4_xboole_0(X36,k4_xboole_0(X36,X37))) ),
    inference(superposition,[],[f2604,f899])).

fof(f899,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f36,f17])).

fof(f2604,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(forward_demodulation,[],[f2538,f1071])).

fof(f2538,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f1071,f110])).

fof(f80102,plain,(
    ! [X118,X116,X117] : k2_xboole_0(k4_xboole_0(X116,k2_xboole_0(X117,k4_xboole_0(X116,X118))),X118) = X118 ),
    inference(forward_demodulation,[],[f80101,f107])).

fof(f80101,plain,(
    ! [X118,X116,X117] : k2_xboole_0(k4_xboole_0(X116,k2_xboole_0(X117,k4_xboole_0(X116,k2_xboole_0(X118,X117)))),X118) = X118 ),
    inference(forward_demodulation,[],[f79702,f20])).

fof(f79702,plain,(
    ! [X118,X116,X117] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X116,X117),k4_xboole_0(X116,k2_xboole_0(X118,X117))),X118) = X118 ),
    inference(superposition,[],[f77998,f16507])).

fof(f77998,plain,(
    ! [X85,X84] : k2_xboole_0(k4_xboole_0(X85,k4_xboole_0(X85,X84)),X84) = X84 ),
    inference(superposition,[],[f65,f77444])).

fof(f100915,plain,(
    ! [X225,X223,X224] : k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(k2_xboole_0(X223,X225),X224),X223)) ),
    inference(forward_demodulation,[],[f100914,f54962])).

fof(f100914,plain,(
    ! [X225,X223,X224] : k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(X224,k2_xboole_0(X223,k2_xboole_0(X223,X225))),X223)) ),
    inference(forward_demodulation,[],[f100913,f21992])).

fof(f100913,plain,(
    ! [X225,X223,X224] : k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(X224,k2_xboole_0(k2_xboole_0(X223,X223),X225)),X223)) ),
    inference(forward_demodulation,[],[f100912,f21992])).

fof(f100912,plain,(
    ! [X225,X223,X224] : k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X223,X223),X224),X225),X223)) ),
    inference(forward_demodulation,[],[f100401,f104])).

fof(f100401,plain,(
    ! [X225,X223,X224] : k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X223,X223),X224),X225),k2_xboole_0(X223,X223))) ),
    inference(superposition,[],[f1120,f122])).

fof(f122,plain,(
    ! [X8,X7] : k2_xboole_0(k2_xboole_0(X8,X8),X7) = k2_xboole_0(k2_xboole_0(X8,X8),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f18,f104])).

fof(f1120,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X4,k4_xboole_0(X5,X3)) = k2_xboole_0(X4,k4_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X3)) ),
    inference(forward_demodulation,[],[f1085,f107])).

fof(f1085,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X4,k4_xboole_0(X5,k2_xboole_0(X3,X4))) = k2_xboole_0(X4,k4_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X3)) ),
    inference(superposition,[],[f107,f34])).

fof(f32,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_1
  <=> k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f33,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:12:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (5372)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (5372)Refutation not found, incomplete strategy% (5372)------------------------------
% 0.22/0.48  % (5372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5372)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (5372)Memory used [KB]: 10490
% 0.22/0.48  % (5372)Time elapsed: 0.059 s
% 0.22/0.48  % (5372)------------------------------
% 0.22/0.48  % (5372)------------------------------
% 0.22/0.49  % (5380)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (5386)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (5386)Refutation not found, incomplete strategy% (5386)------------------------------
% 0.22/0.50  % (5386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5386)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5386)Memory used [KB]: 6012
% 0.22/0.50  % (5386)Time elapsed: 0.053 s
% 0.22/0.50  % (5386)------------------------------
% 0.22/0.50  % (5386)------------------------------
% 0.22/0.50  % (5390)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (5371)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (5371)Refutation not found, incomplete strategy% (5371)------------------------------
% 0.22/0.51  % (5371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (5371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (5371)Memory used [KB]: 6140
% 0.22/0.51  % (5371)Time elapsed: 0.078 s
% 0.22/0.51  % (5371)------------------------------
% 0.22/0.51  % (5371)------------------------------
% 0.22/0.51  % (5377)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (5383)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (5378)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (5382)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (5391)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (5391)Refutation not found, incomplete strategy% (5391)------------------------------
% 0.22/0.52  % (5391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5391)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (5391)Memory used [KB]: 10490
% 0.22/0.52  % (5391)Time elapsed: 0.084 s
% 0.22/0.52  % (5391)------------------------------
% 0.22/0.52  % (5391)------------------------------
% 0.22/0.52  % (5376)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (5375)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (5379)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (5382)Refutation not found, incomplete strategy% (5382)------------------------------
% 0.22/0.53  % (5382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5382)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5382)Memory used [KB]: 10618
% 0.22/0.53  % (5382)Time elapsed: 0.090 s
% 0.22/0.53  % (5382)------------------------------
% 0.22/0.53  % (5382)------------------------------
% 0.22/0.54  % (5384)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.54  % (5384)Refutation not found, incomplete strategy% (5384)------------------------------
% 0.22/0.54  % (5384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5384)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5384)Memory used [KB]: 1535
% 0.22/0.54  % (5384)Time elapsed: 0.108 s
% 0.22/0.54  % (5384)------------------------------
% 0.22/0.54  % (5384)------------------------------
% 0.22/0.54  % (5388)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.54  % (5373)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.55  % (5381)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.55  % (5374)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (5385)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.55  % (5374)Refutation not found, incomplete strategy% (5374)------------------------------
% 0.22/0.55  % (5374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5374)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5374)Memory used [KB]: 10618
% 0.22/0.55  % (5374)Time elapsed: 0.110 s
% 0.22/0.55  % (5374)------------------------------
% 0.22/0.55  % (5374)------------------------------
% 0.22/0.55  % (5387)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.55  % (5389)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.61/0.57  % (5381)Refutation not found, incomplete strategy% (5381)------------------------------
% 1.61/0.57  % (5381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (5381)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (5381)Memory used [KB]: 6012
% 1.61/0.57  % (5381)Time elapsed: 0.135 s
% 1.61/0.57  % (5381)------------------------------
% 1.61/0.57  % (5381)------------------------------
% 4.22/0.93  % (5383)Time limit reached!
% 4.22/0.93  % (5383)------------------------------
% 4.22/0.93  % (5383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.93  % (5383)Termination reason: Time limit
% 4.22/0.93  % (5383)Termination phase: Saturation
% 4.22/0.93  
% 4.22/0.93  % (5383)Memory used [KB]: 12792
% 4.22/0.93  % (5383)Time elapsed: 0.500 s
% 4.22/0.93  % (5383)------------------------------
% 4.22/0.93  % (5383)------------------------------
% 4.22/0.93  % (5376)Time limit reached!
% 4.22/0.93  % (5376)------------------------------
% 4.22/0.93  % (5376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.93  % (5376)Termination reason: Time limit
% 4.22/0.93  % (5376)Termination phase: Saturation
% 4.22/0.93  
% 4.22/0.93  % (5376)Memory used [KB]: 12281
% 4.22/0.93  % (5376)Time elapsed: 0.500 s
% 4.22/0.93  % (5376)------------------------------
% 4.22/0.93  % (5376)------------------------------
% 5.14/1.04  % (5379)Time limit reached!
% 5.14/1.04  % (5379)------------------------------
% 5.14/1.04  % (5379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.14/1.05  % (5379)Termination reason: Time limit
% 5.14/1.05  % (5379)Termination phase: Saturation
% 5.14/1.05  
% 5.14/1.05  % (5379)Memory used [KB]: 13944
% 5.14/1.05  % (5379)Time elapsed: 0.600 s
% 5.14/1.05  % (5379)------------------------------
% 5.14/1.05  % (5379)------------------------------
% 7.17/1.33  % (5380)Time limit reached!
% 7.17/1.33  % (5380)------------------------------
% 7.17/1.33  % (5380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.17/1.33  % (5380)Termination reason: Time limit
% 7.17/1.33  % (5380)Termination phase: Saturation
% 7.17/1.33  
% 7.17/1.33  % (5380)Memory used [KB]: 35692
% 7.17/1.33  % (5380)Time elapsed: 0.900 s
% 7.17/1.33  % (5380)------------------------------
% 7.17/1.33  % (5380)------------------------------
% 9.18/1.54  % (5373)Time limit reached!
% 9.18/1.54  % (5373)------------------------------
% 9.18/1.54  % (5373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.18/1.54  % (5373)Termination reason: Time limit
% 9.18/1.54  % (5373)Termination phase: Saturation
% 9.18/1.54  
% 9.18/1.54  % (5373)Memory used [KB]: 30831
% 9.18/1.54  % (5373)Time elapsed: 1.100 s
% 9.18/1.54  % (5373)------------------------------
% 9.18/1.54  % (5373)------------------------------
% 13.51/2.05  % (5375)Time limit reached!
% 13.51/2.05  % (5375)------------------------------
% 13.51/2.05  % (5375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.51/2.05  % (5375)Termination reason: Time limit
% 13.51/2.05  % (5375)Termination phase: Saturation
% 13.51/2.05  
% 13.51/2.05  % (5375)Memory used [KB]: 6908
% 13.51/2.05  % (5375)Time elapsed: 1.600 s
% 13.51/2.05  % (5375)------------------------------
% 13.51/2.05  % (5375)------------------------------
% 14.23/2.18  % (5378)Time limit reached!
% 14.23/2.18  % (5378)------------------------------
% 14.23/2.18  % (5378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.23/2.18  % (5378)Termination reason: Time limit
% 14.23/2.18  % (5378)Termination phase: Saturation
% 14.23/2.18  
% 14.23/2.18  % (5378)Memory used [KB]: 47078
% 14.23/2.18  % (5378)Time elapsed: 1.700 s
% 14.23/2.18  % (5378)------------------------------
% 14.23/2.18  % (5378)------------------------------
% 19.85/3.08  % (5377)Refutation found. Thanks to Tanya!
% 19.85/3.08  % SZS status Theorem for theBenchmark
% 19.85/3.08  % SZS output start Proof for theBenchmark
% 19.85/3.08  fof(f101147,plain,(
% 19.85/3.08    $false),
% 19.85/3.08    inference(avatar_sat_refutation,[],[f33,f100921])).
% 19.85/3.08  fof(f100921,plain,(
% 19.85/3.08    spl4_1),
% 19.85/3.08    inference(avatar_contradiction_clause,[],[f100920])).
% 19.85/3.08  fof(f100920,plain,(
% 19.85/3.08    $false | spl4_1),
% 19.85/3.08    inference(subsumption_resolution,[],[f32,f100919])).
% 19.85/3.08  fof(f100919,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k4_xboole_0(k2_xboole_0(X224,X225),X223) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,X223))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100918,f104])).
% 19.85/3.08  fof(f104,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,X1))) )),
% 19.85/3.08    inference(superposition,[],[f20,f47])).
% 19.85/3.08  fof(f47,plain,(
% 19.85/3.08    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f43,f34])).
% 19.85/3.08  fof(f34,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 19.85/3.08    inference(superposition,[],[f19,f17])).
% 19.85/3.08  fof(f17,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.85/3.08    inference(cnf_transformation,[],[f1])).
% 19.85/3.08  fof(f1,axiom,(
% 19.85/3.08    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.85/3.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 19.85/3.08  fof(f19,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 19.85/3.08    inference(cnf_transformation,[],[f4])).
% 19.85/3.08  fof(f4,axiom,(
% 19.85/3.08    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 19.85/3.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 19.85/3.08  fof(f43,plain,(
% 19.85/3.08    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4)) )),
% 19.85/3.08    inference(superposition,[],[f34,f18])).
% 19.85/3.08  fof(f18,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.85/3.08    inference(cnf_transformation,[],[f3])).
% 19.85/3.08  fof(f3,axiom,(
% 19.85/3.08    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.85/3.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 19.85/3.08  fof(f20,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 19.85/3.08    inference(cnf_transformation,[],[f5])).
% 19.85/3.08  fof(f5,axiom,(
% 19.85/3.08    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 19.85/3.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 19.85/3.08  fof(f100918,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k4_xboole_0(k2_xboole_0(X224,X225),X223)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100917,f54962])).
% 19.85/3.08  fof(f54962,plain,(
% 19.85/3.08    ( ! [X269,X267,X268] : (k4_xboole_0(k2_xboole_0(X268,X269),X267) = k4_xboole_0(k2_xboole_0(X269,k2_xboole_0(X267,X268)),X267)) )),
% 19.85/3.08    inference(superposition,[],[f34,f45592])).
% 19.85/3.08  fof(f45592,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(X45,k2_xboole_0(X43,X44)) = k2_xboole_0(X44,k2_xboole_0(X45,X43))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f45591,f3332])).
% 19.85/3.08  fof(f3332,plain,(
% 19.85/3.08    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 19.85/3.08    inference(forward_demodulation,[],[f3286,f3199])).
% 19.85/3.08  fof(f3199,plain,(
% 19.85/3.08    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,X10)) = X9) )),
% 19.85/3.08    inference(resolution,[],[f3094,f1053])).
% 19.85/3.08  fof(f1053,plain,(
% 19.85/3.08    ( ! [X4,X3] : (r2_hidden(sK3(X3,X4,X3),X4) | k4_xboole_0(X3,X4) = X3) )),
% 19.85/3.08    inference(global_subsumption,[],[f283,f1051])).
% 19.85/3.08  fof(f1051,plain,(
% 19.85/3.08    ( ! [X4,X3] : (r2_hidden(sK3(X3,X4,X3),X4) | ~r2_hidden(sK3(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3) )),
% 19.85/3.08    inference(duplicate_literal_removal,[],[f1047])).
% 19.85/3.08  fof(f1047,plain,(
% 19.85/3.08    ( ! [X4,X3] : (r2_hidden(sK3(X3,X4,X3),X4) | ~r2_hidden(sK3(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3 | k4_xboole_0(X3,X4) = X3) )),
% 19.85/3.08    inference(resolution,[],[f26,f283])).
% 19.85/3.08  fof(f26,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 19.85/3.08    inference(cnf_transformation,[],[f15])).
% 19.85/3.08  fof(f15,plain,(
% 19.85/3.08    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.85/3.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).
% 19.85/3.08  fof(f14,plain,(
% 19.85/3.08    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 19.85/3.08    introduced(choice_axiom,[])).
% 19.85/3.08  fof(f13,plain,(
% 19.85/3.08    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.85/3.08    inference(rectify,[],[f12])).
% 19.85/3.08  fof(f12,plain,(
% 19.85/3.08    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.85/3.08    inference(flattening,[],[f11])).
% 19.85/3.08  fof(f11,plain,(
% 19.85/3.08    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.85/3.08    inference(nnf_transformation,[],[f2])).
% 19.85/3.08  fof(f2,axiom,(
% 19.85/3.08    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.85/3.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 19.85/3.08  fof(f283,plain,(
% 19.85/3.08    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 19.85/3.08    inference(factoring,[],[f24])).
% 19.85/3.08  fof(f24,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 19.85/3.08    inference(cnf_transformation,[],[f15])).
% 19.85/3.08  fof(f3094,plain,(
% 19.85/3.08    ( ! [X10,X11] : (~r2_hidden(X11,k4_xboole_0(X10,X10))) )),
% 19.85/3.08    inference(superposition,[],[f3011,f104])).
% 19.85/3.08  fof(f3011,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) )),
% 19.85/3.08    inference(superposition,[],[f2977,f65])).
% 19.85/3.08  fof(f65,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 19.85/3.08    inference(superposition,[],[f48,f17])).
% 19.85/3.08  fof(f48,plain,(
% 19.85/3.08    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f44,f18])).
% 19.85/3.08  fof(f44,plain,(
% 19.85/3.08    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 19.85/3.08    inference(superposition,[],[f18,f34])).
% 19.85/3.08  fof(f2977,plain,(
% 19.85/3.08    ( ! [X39,X41,X42,X40] : (~r2_hidden(X41,k4_xboole_0(X39,k2_xboole_0(X39,k2_xboole_0(X40,X42))))) )),
% 19.85/3.08    inference(subsumption_resolution,[],[f2916,f2970])).
% 19.85/3.08  fof(f2970,plain,(
% 19.85/3.08    ( ! [X39,X37,X41,X38,X40] : (~r2_hidden(X37,k4_xboole_0(X38,k2_xboole_0(X39,X38))) | ~r2_hidden(X37,k4_xboole_0(X40,k2_xboole_0(X39,X41)))) )),
% 19.85/3.08    inference(resolution,[],[f2837,f758])).
% 19.85/3.08  fof(f758,plain,(
% 19.85/3.08    ( ! [X14,X12,X15,X13] : (~r2_hidden(X12,X14) | ~r2_hidden(X12,k4_xboole_0(X13,k2_xboole_0(X14,X15)))) )),
% 19.85/3.08    inference(resolution,[],[f108,f28])).
% 19.85/3.08  fof(f28,plain,(
% 19.85/3.08    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 19.85/3.08    inference(equality_resolution,[],[f22])).
% 19.85/3.08  fof(f22,plain,(
% 19.85/3.08    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.85/3.08    inference(cnf_transformation,[],[f15])).
% 19.85/3.08  fof(f108,plain,(
% 19.85/3.08    ( ! [X10,X8,X11,X9] : (r2_hidden(X11,k4_xboole_0(X8,X9)) | ~r2_hidden(X11,k4_xboole_0(X8,k2_xboole_0(X9,X10)))) )),
% 19.85/3.08    inference(superposition,[],[f29,f20])).
% 19.85/3.08  fof(f29,plain,(
% 19.85/3.08    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 19.85/3.08    inference(equality_resolution,[],[f21])).
% 19.85/3.08  fof(f21,plain,(
% 19.85/3.08    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.85/3.08    inference(cnf_transformation,[],[f15])).
% 19.85/3.08  fof(f2837,plain,(
% 19.85/3.08    ( ! [X24,X23,X22] : (r2_hidden(X24,X22) | ~r2_hidden(X24,k4_xboole_0(X23,k2_xboole_0(X22,X23)))) )),
% 19.85/3.08    inference(superposition,[],[f29,f2712])).
% 19.85/3.08  fof(f2712,plain,(
% 19.85/3.08    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X3,X4)) = k4_xboole_0(X4,k2_xboole_0(X3,X4))) )),
% 19.85/3.08    inference(superposition,[],[f1171,f111])).
% 19.85/3.08  fof(f111,plain,(
% 19.85/3.08    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(X4,k2_xboole_0(X3,X5))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f101,f20])).
% 19.85/3.08  fof(f101,plain,(
% 19.85/3.08    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(k4_xboole_0(X4,X3),X5)) )),
% 19.85/3.08    inference(superposition,[],[f20,f34])).
% 19.85/3.08  fof(f1171,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X0))) )),
% 19.85/3.08    inference(superposition,[],[f110,f17])).
% 19.85/3.08  fof(f110,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100,f20])).
% 19.85/3.08  fof(f100,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 19.85/3.08    inference(superposition,[],[f20,f19])).
% 19.85/3.08  fof(f2916,plain,(
% 19.85/3.08    ( ! [X39,X41,X42,X40] : (~r2_hidden(X41,k4_xboole_0(X39,k2_xboole_0(X39,k2_xboole_0(X40,X42)))) | r2_hidden(X41,k4_xboole_0(X40,k2_xboole_0(X39,X40)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f2844,f114])).
% 19.85/3.08  fof(f114,plain,(
% 19.85/3.08    ( ! [X12,X10,X11,X9] : (k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) = k4_xboole_0(X9,k2_xboole_0(X10,k2_xboole_0(X11,X12)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f113,f20])).
% 19.85/3.08  fof(f113,plain,(
% 19.85/3.08    ( ! [X12,X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f103,f20])).
% 19.85/3.08  fof(f103,plain,(
% 19.85/3.08    ( ! [X12,X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X12)) )),
% 19.85/3.08    inference(superposition,[],[f20,f20])).
% 19.85/3.08  fof(f2844,plain,(
% 19.85/3.08    ( ! [X39,X41,X42,X40] : (r2_hidden(X41,k4_xboole_0(X40,k2_xboole_0(X39,X40))) | ~r2_hidden(X41,k4_xboole_0(X39,k2_xboole_0(k2_xboole_0(X39,X40),X42)))) )),
% 19.85/3.08    inference(superposition,[],[f108,f2712])).
% 19.85/3.08  fof(f3286,plain,(
% 19.85/3.08    ( ! [X0] : (k2_xboole_0(X0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 19.85/3.08    inference(superposition,[],[f3199,f36])).
% 19.85/3.08  fof(f36,plain,(
% 19.85/3.08    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 19.85/3.08    inference(superposition,[],[f19,f18])).
% 19.85/3.08  fof(f45591,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(X44,k2_xboole_0(X45,X43)) = k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f45590,f45049])).
% 19.85/3.08  fof(f45049,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(X44,k2_xboole_0(X45,X43)) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X44,k2_xboole_0(X45,X43)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f45048,f48])).
% 19.85/3.08  fof(f45048,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(X44,k2_xboole_0(X44,k2_xboole_0(X45,X43))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X44,k2_xboole_0(X44,k2_xboole_0(X45,X43))))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f45047,f34636])).
% 19.85/3.08  fof(f34636,plain,(
% 19.85/3.08    ( ! [X557,X559,X556,X558] : (k2_xboole_0(k2_xboole_0(X559,X558),k2_xboole_0(X556,X557)) = k2_xboole_0(X558,k2_xboole_0(X559,k2_xboole_0(X557,X556)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f34250,f25344])).
% 19.85/3.08  fof(f25344,plain,(
% 19.85/3.08    ( ! [X239,X237,X236] : (k2_xboole_0(X237,k2_xboole_0(X236,X239)) = k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(X237,X236)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f25343,f3601])).
% 19.85/3.08  fof(f3601,plain,(
% 19.85/3.08    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1) )),
% 19.85/3.08    inference(forward_demodulation,[],[f3528,f34])).
% 19.85/3.08  fof(f3528,plain,(
% 19.85/3.08    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1) )),
% 19.85/3.08    inference(superposition,[],[f3335,f107])).
% 19.85/3.08  fof(f107,plain,(
% 19.85/3.08    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 19.85/3.08    inference(superposition,[],[f18,f20])).
% 19.85/3.08  fof(f3335,plain,(
% 19.85/3.08    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X5,X5)) = X4) )),
% 19.85/3.08    inference(forward_demodulation,[],[f3289,f3199])).
% 19.85/3.08  fof(f3289,plain,(
% 19.85/3.08    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X5,X5)) = k4_xboole_0(X4,k4_xboole_0(X5,X5))) )),
% 19.85/3.08    inference(superposition,[],[f3199,f19])).
% 19.85/3.08  fof(f25343,plain,(
% 19.85/3.08    ( ! [X239,X237,X238,X236] : (k2_xboole_0(X237,k2_xboole_0(X236,X239)) = k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(X237,k2_xboole_0(X236,k4_xboole_0(X236,X238)))))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f25342,f16838])).
% 19.85/3.08  fof(f16838,plain,(
% 19.85/3.08    ( ! [X173,X176,X174] : (k2_xboole_0(X176,k2_xboole_0(X173,X174)) = k2_xboole_0(X176,k2_xboole_0(X174,X173))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f16693,f3334])).
% 19.85/3.08  fof(f3334,plain,(
% 19.85/3.08    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X2),X3) = X3) )),
% 19.85/3.08    inference(forward_demodulation,[],[f3288,f3199])).
% 19.85/3.08  fof(f3288,plain,(
% 19.85/3.08    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X2),X3) = k4_xboole_0(X3,k4_xboole_0(X2,X2))) )),
% 19.85/3.08    inference(superposition,[],[f3199,f34])).
% 19.85/3.08  fof(f16693,plain,(
% 19.85/3.08    ( ! [X175,X173,X176,X174] : (k2_xboole_0(k2_xboole_0(k4_xboole_0(X175,X175),X176),k2_xboole_0(X173,X174)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X175,X175),X176),k2_xboole_0(X174,X173))) )),
% 19.85/3.08    inference(superposition,[],[f1232,f15295])).
% 19.85/3.08  fof(f15295,plain,(
% 19.85/3.08    ( ! [X144,X142,X143] : (k2_xboole_0(X142,X143) = k2_xboole_0(k2_xboole_0(X143,X142),k4_xboole_0(X144,X144))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f15045,f58])).
% 19.85/3.08  fof(f58,plain,(
% 19.85/3.08    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f57,f40])).
% 19.85/3.08  fof(f40,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f37,f18])).
% 19.85/3.08  fof(f37,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 19.85/3.08    inference(superposition,[],[f18,f19])).
% 19.85/3.08  fof(f57,plain,(
% 19.85/3.08    ( ! [X6,X7] : (k2_xboole_0(X6,k2_xboole_0(X7,X6)) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f52,f17])).
% 19.85/3.08  fof(f52,plain,(
% 19.85/3.08    ( ! [X6,X7] : (k2_xboole_0(k2_xboole_0(X7,X6),X6) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 19.85/3.08    inference(superposition,[],[f40,f40])).
% 19.85/3.08  fof(f15045,plain,(
% 19.85/3.08    ( ! [X144,X142,X143] : (k2_xboole_0(k2_xboole_0(X143,X142),k4_xboole_0(X144,X144)) = k2_xboole_0(k2_xboole_0(X143,X142),k2_xboole_0(X142,X143))) )),
% 19.85/3.08    inference(superposition,[],[f1113,f3536])).
% 19.85/3.08  fof(f3536,plain,(
% 19.85/3.08    ( ! [X28,X27] : (k4_xboole_0(X27,X27) = k4_xboole_0(X28,X28)) )),
% 19.85/3.08    inference(superposition,[],[f3335,f3334])).
% 19.85/3.08  fof(f1113,plain,(
% 19.85/3.08    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X17,X16),k4_xboole_0(X18,k2_xboole_0(X16,X17))) = k2_xboole_0(k2_xboole_0(X17,X16),X18)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f1076,f1112])).
% 19.85/3.08  fof(f1112,plain,(
% 19.85/3.08    ( ! [X14,X15,X13] : (k2_xboole_0(k2_xboole_0(X14,X13),k4_xboole_0(X15,X13)) = k2_xboole_0(k2_xboole_0(X14,X13),X15)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f1075,f18])).
% 19.85/3.08  fof(f1075,plain,(
% 19.85/3.08    ( ! [X14,X15,X13] : (k2_xboole_0(k2_xboole_0(X14,X13),k4_xboole_0(X15,X13)) = k2_xboole_0(k2_xboole_0(X14,X13),k4_xboole_0(X15,k2_xboole_0(X14,X13)))) )),
% 19.85/3.08    inference(superposition,[],[f107,f65])).
% 19.85/3.08  fof(f1076,plain,(
% 19.85/3.08    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X17,X16),k4_xboole_0(X18,X16)) = k2_xboole_0(k2_xboole_0(X17,X16),k4_xboole_0(X18,k2_xboole_0(X16,X17)))) )),
% 19.85/3.08    inference(superposition,[],[f107,f40])).
% 19.85/3.08  fof(f1232,plain,(
% 19.85/3.08    ( ! [X10,X11,X9] : (k2_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(X10,X11),X9)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f1197,f18])).
% 19.85/3.08  fof(f1197,plain,(
% 19.85/3.08    ( ! [X10,X11,X9] : (k2_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X9,k2_xboole_0(X10,X11)))) )),
% 19.85/3.08    inference(superposition,[],[f18,f110])).
% 19.85/3.08  fof(f25342,plain,(
% 19.85/3.08    ( ! [X239,X237,X238,X236] : (k2_xboole_0(X237,k2_xboole_0(X236,X239)) = k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(X237,k2_xboole_0(k4_xboole_0(X236,X238),X236))))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f25341,f114])).
% 19.85/3.08  fof(f25341,plain,(
% 19.85/3.08    ( ! [X239,X237,X238,X236] : (k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(k2_xboole_0(X237,k4_xboole_0(X236,X238)),X236))) = k2_xboole_0(X237,k2_xboole_0(X236,X239))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f25147,f21992])).
% 19.85/3.08  fof(f21992,plain,(
% 19.85/3.08    ( ! [X14,X12,X13] : (k2_xboole_0(X13,k2_xboole_0(X12,X14)) = k2_xboole_0(k2_xboole_0(X12,X13),X14)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f21991,f21396])).
% 19.85/3.08  fof(f21396,plain,(
% 19.85/3.08    ( ! [X24,X23] : (k2_xboole_0(X24,X23) = k2_xboole_0(k4_xboole_0(X24,X23),X23)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f21236,f5842])).
% 19.85/3.08  fof(f5842,plain,(
% 19.85/3.08    ( ! [X80,X78,X79] : (k2_xboole_0(X78,X79) = k4_xboole_0(k2_xboole_0(X79,X78),k4_xboole_0(X80,X80))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f5841,f3199])).
% 19.85/3.08  fof(f5841,plain,(
% 19.85/3.08    ( ! [X80,X78,X79] : (k4_xboole_0(k2_xboole_0(X79,X78),k4_xboole_0(X80,X80)) = k4_xboole_0(k2_xboole_0(X78,X79),k4_xboole_0(X80,X80))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f5840,f40])).
% 19.85/3.08  fof(f5840,plain,(
% 19.85/3.08    ( ! [X80,X78,X79] : (k4_xboole_0(k2_xboole_0(X79,X78),k4_xboole_0(X80,X80)) = k4_xboole_0(k2_xboole_0(X78,k2_xboole_0(X79,X78)),k4_xboole_0(X80,X80))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f5793,f17])).
% 19.85/3.08  fof(f5793,plain,(
% 19.85/3.08    ( ! [X80,X78,X79] : (k4_xboole_0(k2_xboole_0(X79,X78),k4_xboole_0(X80,X80)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X79,X78),X78),k4_xboole_0(X80,X80))) )),
% 19.85/3.08    inference(superposition,[],[f36,f3631])).
% 19.85/3.08  fof(f3631,plain,(
% 19.85/3.08    ( ! [X6,X4,X5] : (k4_xboole_0(X6,X6) = k4_xboole_0(X5,k2_xboole_0(X4,X5))) )),
% 19.85/3.08    inference(superposition,[],[f3536,f111])).
% 19.85/3.08  fof(f21236,plain,(
% 19.85/3.08    ( ! [X24,X23,X25] : (k2_xboole_0(k4_xboole_0(X24,X23),X23) = k4_xboole_0(k2_xboole_0(X23,X24),k4_xboole_0(X25,X25))) )),
% 19.85/3.08    inference(superposition,[],[f5842,f18])).
% 19.85/3.08  fof(f21991,plain,(
% 19.85/3.08    ( ! [X14,X12,X13] : (k2_xboole_0(k4_xboole_0(X13,k2_xboole_0(X12,X14)),k2_xboole_0(X12,X14)) = k2_xboole_0(k2_xboole_0(X12,X13),X14)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f21758,f1399])).
% 19.85/3.08  fof(f1399,plain,(
% 19.85/3.08    ( ! [X14,X12,X13] : (k2_xboole_0(k2_xboole_0(X12,X14),k2_xboole_0(X12,X13)) = k2_xboole_0(k2_xboole_0(X12,X14),X13)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f1364,f18])).
% 19.85/3.08  fof(f1364,plain,(
% 19.85/3.08    ( ! [X14,X12,X13] : (k2_xboole_0(k2_xboole_0(X12,X14),k2_xboole_0(X12,X13)) = k2_xboole_0(k2_xboole_0(X12,X14),k4_xboole_0(X13,k2_xboole_0(X12,X14)))) )),
% 19.85/3.08    inference(superposition,[],[f18,f111])).
% 19.85/3.08  fof(f21758,plain,(
% 19.85/3.08    ( ! [X14,X12,X13] : (k2_xboole_0(k4_xboole_0(X13,k2_xboole_0(X12,X14)),k2_xboole_0(X12,X14)) = k2_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X12,X14))) )),
% 19.85/3.08    inference(superposition,[],[f21396,f111])).
% 19.85/3.08  fof(f25147,plain,(
% 19.85/3.08    ( ! [X239,X237,X238,X236] : (k2_xboole_0(k2_xboole_0(X236,X237),k4_xboole_0(X239,k2_xboole_0(k2_xboole_0(X237,k4_xboole_0(X236,X238)),X236))) = k2_xboole_0(k2_xboole_0(X236,X237),X239)) )),
% 19.85/3.08    inference(superposition,[],[f1113,f7485])).
% 19.85/3.08  fof(f7485,plain,(
% 19.85/3.08    ( ! [X101,X102,X100] : (k2_xboole_0(X100,X102) = k2_xboole_0(X100,k2_xboole_0(X102,k4_xboole_0(X100,X101)))) )),
% 19.85/3.08    inference(superposition,[],[f1232,f3799])).
% 19.85/3.08  fof(f3799,plain,(
% 19.85/3.08    ( ! [X33,X32] : (k2_xboole_0(k4_xboole_0(X32,X33),X32) = X32) )),
% 19.85/3.08    inference(superposition,[],[f65,f3601])).
% 19.85/3.08  fof(f34250,plain,(
% 19.85/3.08    ( ! [X557,X559,X556,X558] : (k2_xboole_0(k2_xboole_0(X559,X558),k2_xboole_0(X556,X557)) = k2_xboole_0(k2_xboole_0(X559,X558),k4_xboole_0(k2_xboole_0(X557,X556),k2_xboole_0(X558,X559)))) )),
% 19.85/3.08    inference(superposition,[],[f1113,f16652])).
% 19.85/3.08  fof(f16652,plain,(
% 19.85/3.08    ( ! [X35,X33,X34] : (k4_xboole_0(k2_xboole_0(X33,X34),X35) = k4_xboole_0(k2_xboole_0(X34,X33),X35)) )),
% 19.85/3.08    inference(superposition,[],[f3816,f15295])).
% 19.85/3.08  fof(f3816,plain,(
% 19.85/3.08    ( ! [X83,X84,X82] : (k4_xboole_0(X84,X82) = k4_xboole_0(k2_xboole_0(X84,k4_xboole_0(X82,X83)),X82)) )),
% 19.85/3.08    inference(superposition,[],[f1171,f3601])).
% 19.85/3.08  fof(f45047,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(k2_xboole_0(X44,X44),k2_xboole_0(X43,X45)) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(k2_xboole_0(X44,X44),k2_xboole_0(X43,X45)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f44682,f21992])).
% 19.85/3.08  fof(f44682,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(k2_xboole_0(X43,k2_xboole_0(X44,X44)),X45) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(k2_xboole_0(X43,k2_xboole_0(X44,X44)),X45))) )),
% 19.85/3.08    inference(superposition,[],[f25547,f128])).
% 19.85/3.08  fof(f128,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f115,f104])).
% 19.85/3.08  fof(f115,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1)) )),
% 19.85/3.08    inference(superposition,[],[f104,f19])).
% 19.85/3.08  fof(f25547,plain,(
% 19.85/3.08    ( ! [X50,X51,X49] : (k2_xboole_0(X49,X50) = k2_xboole_0(k4_xboole_0(X49,X51),k2_xboole_0(X49,X50))) )),
% 19.85/3.08    inference(superposition,[],[f7640,f17])).
% 19.85/3.08  fof(f7640,plain,(
% 19.85/3.08    ( ! [X101,X102,X100] : (k2_xboole_0(X100,X102) = k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X100,X101))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f7639,f48])).
% 19.85/3.08  fof(f7639,plain,(
% 19.85/3.08    ( ! [X101,X102,X100] : (k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X100,X101)) = k2_xboole_0(X100,k2_xboole_0(X100,X102))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f7509,f17])).
% 19.85/3.08  fof(f7509,plain,(
% 19.85/3.08    ( ! [X101,X102,X100] : (k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X100,X101)) = k2_xboole_0(k2_xboole_0(X100,X102),X100)) )),
% 19.85/3.08    inference(superposition,[],[f1232,f3799])).
% 19.85/3.08  fof(f45590,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X44,k2_xboole_0(X45,X43)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f45589,f48])).
% 19.85/3.08  fof(f45589,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(X44,k2_xboole_0(X44,k2_xboole_0(X45,X43))))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f45588,f34636])).
% 19.85/3.08  fof(f45588,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(k2_xboole_0(X44,X44),k2_xboole_0(X43,X45)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f45202,f21992])).
% 19.85/3.08  fof(f45202,plain,(
% 19.85/3.08    ( ! [X45,X43,X44] : (k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,X44))) = k2_xboole_0(k4_xboole_0(X43,X44),k2_xboole_0(k2_xboole_0(X43,k2_xboole_0(X44,X44)),X45))) )),
% 19.85/3.08    inference(superposition,[],[f25763,f128])).
% 19.85/3.08  fof(f25763,plain,(
% 19.85/3.08    ( ! [X449,X448,X450] : (k2_xboole_0(k4_xboole_0(X448,X450),k2_xboole_0(X448,X449)) = k2_xboole_0(X449,X448)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f25651,f5842])).
% 19.85/3.08  fof(f25651,plain,(
% 19.85/3.08    ( ! [X449,X451,X448,X450] : (k2_xboole_0(k4_xboole_0(X448,X450),k2_xboole_0(X448,X449)) = k4_xboole_0(k2_xboole_0(X448,X449),k4_xboole_0(X451,X451))) )),
% 19.85/3.08    inference(superposition,[],[f5842,f7640])).
% 19.85/3.08  fof(f100917,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k4_xboole_0(k2_xboole_0(X225,k2_xboole_0(X223,X224)),X223)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100916,f21992])).
% 19.85/3.08  fof(f100916,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X223,X225),X224),X223)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100915,f90531])).
% 19.85/3.08  fof(f90531,plain,(
% 19.85/3.08    ( ! [X94,X92,X93] : (k4_xboole_0(k2_xboole_0(X94,X93),X92) = k2_xboole_0(k4_xboole_0(X93,X92),k4_xboole_0(k2_xboole_0(X94,X93),X92))) )),
% 19.85/3.08    inference(superposition,[],[f80102,f88779])).
% 19.85/3.08  fof(f88779,plain,(
% 19.85/3.08    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X3,X2),X4))) = X4) )),
% 19.85/3.08    inference(superposition,[],[f83225,f17])).
% 19.85/3.08  fof(f83225,plain,(
% 19.85/3.08    ( ! [X6,X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(k2_xboole_0(X6,X7),X8))) = X8) )),
% 19.85/3.08    inference(forward_demodulation,[],[f82903,f13683])).
% 19.85/3.08  fof(f13683,plain,(
% 19.85/3.08    ( ! [X26,X27,X25] : (k4_xboole_0(X25,k2_xboole_0(k4_xboole_0(X26,X25),X27)) = k4_xboole_0(X25,X27)) )),
% 19.85/3.08    inference(superposition,[],[f20,f13466])).
% 19.85/3.08  fof(f13466,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 19.85/3.08    inference(superposition,[],[f13446,f3332])).
% 19.85/3.08  fof(f13446,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0) )),
% 19.85/3.08    inference(duplicate_literal_removal,[],[f13351])).
% 19.85/3.08  fof(f13351,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 | k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0) )),
% 19.85/3.08    inference(resolution,[],[f289,f1053])).
% 19.85/3.08  fof(f289,plain,(
% 19.85/3.08    ( ! [X17,X15,X18,X16] : (~r2_hidden(sK3(X15,X16,X15),k4_xboole_0(X17,k2_xboole_0(X18,X15))) | k4_xboole_0(X15,X16) = X15) )),
% 19.85/3.08    inference(resolution,[],[f283,f109])).
% 19.85/3.08  fof(f109,plain,(
% 19.85/3.08    ( ! [X14,X12,X15,X13] : (~r2_hidden(X15,X14) | ~r2_hidden(X15,k4_xboole_0(X12,k2_xboole_0(X13,X14)))) )),
% 19.85/3.08    inference(superposition,[],[f28,f20])).
% 19.85/3.08  fof(f82903,plain,(
% 19.85/3.08    ( ! [X6,X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(k2_xboole_0(X6,X7),X8)))) = X8) )),
% 19.85/3.08    inference(superposition,[],[f78200,f956])).
% 19.85/3.08  fof(f956,plain,(
% 19.85/3.08    ( ! [X4,X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X3,X2),X4))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f920,f20])).
% 19.85/3.08  fof(f920,plain,(
% 19.85/3.08    ( ! [X4,X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,X2)),X4)) )),
% 19.85/3.08    inference(superposition,[],[f20,f36])).
% 19.85/3.08  fof(f78200,plain,(
% 19.85/3.08    ( ! [X118,X116,X117] : (k2_xboole_0(X118,k4_xboole_0(X116,k2_xboole_0(X117,k4_xboole_0(X116,X118)))) = X118) )),
% 19.85/3.08    inference(forward_demodulation,[],[f78199,f107])).
% 19.85/3.08  fof(f78199,plain,(
% 19.85/3.08    ( ! [X118,X116,X117] : (k2_xboole_0(X118,k4_xboole_0(X116,k2_xboole_0(X117,k4_xboole_0(X116,k2_xboole_0(X118,X117))))) = X118) )),
% 19.85/3.08    inference(forward_demodulation,[],[f77835,f20])).
% 19.85/3.08  fof(f77835,plain,(
% 19.85/3.08    ( ! [X118,X116,X117] : (k2_xboole_0(X118,k4_xboole_0(k4_xboole_0(X116,X117),k4_xboole_0(X116,k2_xboole_0(X118,X117)))) = X118) )),
% 19.85/3.08    inference(superposition,[],[f77444,f16507])).
% 19.85/3.08  fof(f16507,plain,(
% 19.85/3.08    ( ! [X233,X234,X232] : (k4_xboole_0(k4_xboole_0(X233,X232),X234) = k4_xboole_0(X233,k2_xboole_0(X234,X232))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f16375,f2761])).
% 19.85/3.08  fof(f2761,plain,(
% 19.85/3.08    ( ! [X76,X74,X75] : (k4_xboole_0(k4_xboole_0(X74,X75),k2_xboole_0(X76,X75)) = k4_xboole_0(X74,k2_xboole_0(X76,X75))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f2686,f1338])).
% 19.85/3.08  fof(f1338,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X0))) )),
% 19.85/3.08    inference(superposition,[],[f111,f17])).
% 19.85/3.08  fof(f2686,plain,(
% 19.85/3.08    ( ! [X76,X74,X75] : (k4_xboole_0(k4_xboole_0(X74,X75),k2_xboole_0(X76,X75)) = k4_xboole_0(k2_xboole_0(X75,X74),k2_xboole_0(X76,X75))) )),
% 19.85/3.08    inference(superposition,[],[f1171,f955])).
% 19.85/3.08  fof(f955,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 19.85/3.08    inference(forward_demodulation,[],[f954,f56])).
% 19.85/3.08  fof(f56,plain,(
% 19.85/3.08    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f55,f18])).
% 19.85/3.08  fof(f55,plain,(
% 19.85/3.08    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f51,f17])).
% 19.85/3.08  fof(f51,plain,(
% 19.85/3.08    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 19.85/3.08    inference(superposition,[],[f40,f18])).
% 19.85/3.08  fof(f954,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f919,f18])).
% 19.85/3.08  fof(f919,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 19.85/3.08    inference(superposition,[],[f18,f36])).
% 19.85/3.08  fof(f16375,plain,(
% 19.85/3.08    ( ! [X233,X234,X232] : (k4_xboole_0(k4_xboole_0(X233,X232),X234) = k4_xboole_0(k4_xboole_0(X233,X232),k2_xboole_0(X234,X232))) )),
% 19.85/3.08    inference(superposition,[],[f13724,f13466])).
% 19.85/3.08  fof(f13724,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f13674,f1118])).
% 19.85/3.08  fof(f1118,plain,(
% 19.85/3.08    ( ! [X57,X56,X55] : (k2_xboole_0(X56,k4_xboole_0(X57,k4_xboole_0(X55,X56))) = k2_xboole_0(X56,k4_xboole_0(X57,X55))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f1083,f1071])).
% 19.85/3.08  fof(f1071,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) )),
% 19.85/3.08    inference(superposition,[],[f107,f17])).
% 19.85/3.08  fof(f1083,plain,(
% 19.85/3.08    ( ! [X57,X56,X55] : (k2_xboole_0(X56,k4_xboole_0(X57,k4_xboole_0(X55,X56))) = k2_xboole_0(X56,k4_xboole_0(X57,k2_xboole_0(X56,X55)))) )),
% 19.85/3.08    inference(superposition,[],[f107,f955])).
% 19.85/3.08  fof(f13674,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) )),
% 19.85/3.08    inference(superposition,[],[f13466,f20])).
% 19.85/3.08  fof(f77444,plain,(
% 19.85/3.08    ( ! [X37,X36] : (k2_xboole_0(X37,k4_xboole_0(X36,k4_xboole_0(X36,X37))) = X37) )),
% 19.85/3.08    inference(forward_demodulation,[],[f77443,f3601])).
% 19.85/3.08  fof(f77443,plain,(
% 19.85/3.08    ( ! [X37,X36] : (k2_xboole_0(X37,k4_xboole_0(X37,X36)) = k2_xboole_0(X37,k4_xboole_0(X36,k4_xboole_0(X36,X37)))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f77015,f1118])).
% 19.85/3.08  fof(f77015,plain,(
% 19.85/3.08    ( ! [X37,X36] : (k2_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X36,X37))) = k2_xboole_0(X37,k4_xboole_0(X36,k4_xboole_0(X36,X37)))) )),
% 19.85/3.08    inference(superposition,[],[f2604,f899])).
% 19.85/3.08  fof(f899,plain,(
% 19.85/3.08    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 19.85/3.08    inference(superposition,[],[f36,f17])).
% 19.85/3.08  fof(f2604,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X1,k4_xboole_0(X0,X2))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f2538,f1071])).
% 19.85/3.08  fof(f2538,plain,(
% 19.85/3.08    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 19.85/3.08    inference(superposition,[],[f1071,f110])).
% 19.85/3.08  fof(f80102,plain,(
% 19.85/3.08    ( ! [X118,X116,X117] : (k2_xboole_0(k4_xboole_0(X116,k2_xboole_0(X117,k4_xboole_0(X116,X118))),X118) = X118) )),
% 19.85/3.08    inference(forward_demodulation,[],[f80101,f107])).
% 19.85/3.08  fof(f80101,plain,(
% 19.85/3.08    ( ! [X118,X116,X117] : (k2_xboole_0(k4_xboole_0(X116,k2_xboole_0(X117,k4_xboole_0(X116,k2_xboole_0(X118,X117)))),X118) = X118) )),
% 19.85/3.08    inference(forward_demodulation,[],[f79702,f20])).
% 19.85/3.08  fof(f79702,plain,(
% 19.85/3.08    ( ! [X118,X116,X117] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X116,X117),k4_xboole_0(X116,k2_xboole_0(X118,X117))),X118) = X118) )),
% 19.85/3.08    inference(superposition,[],[f77998,f16507])).
% 19.85/3.08  fof(f77998,plain,(
% 19.85/3.08    ( ! [X85,X84] : (k2_xboole_0(k4_xboole_0(X85,k4_xboole_0(X85,X84)),X84) = X84) )),
% 19.85/3.08    inference(superposition,[],[f65,f77444])).
% 19.85/3.08  fof(f100915,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(k2_xboole_0(X223,X225),X224),X223))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100914,f54962])).
% 19.85/3.08  fof(f100914,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(X224,k2_xboole_0(X223,k2_xboole_0(X223,X225))),X223))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100913,f21992])).
% 19.85/3.08  fof(f100913,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(X224,k2_xboole_0(k2_xboole_0(X223,X223),X225)),X223))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100912,f21992])).
% 19.85/3.08  fof(f100912,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X223,X223),X224),X225),X223))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f100401,f104])).
% 19.85/3.08  fof(f100401,plain,(
% 19.85/3.08    ( ! [X225,X223,X224] : (k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(X225,k2_xboole_0(X223,X223))) = k2_xboole_0(k4_xboole_0(X224,X223),k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X223,X223),X224),X225),k2_xboole_0(X223,X223)))) )),
% 19.85/3.08    inference(superposition,[],[f1120,f122])).
% 19.85/3.08  fof(f122,plain,(
% 19.85/3.08    ( ! [X8,X7] : (k2_xboole_0(k2_xboole_0(X8,X8),X7) = k2_xboole_0(k2_xboole_0(X8,X8),k4_xboole_0(X7,X8))) )),
% 19.85/3.08    inference(superposition,[],[f18,f104])).
% 19.85/3.08  fof(f1120,plain,(
% 19.85/3.08    ( ! [X4,X5,X3] : (k2_xboole_0(X4,k4_xboole_0(X5,X3)) = k2_xboole_0(X4,k4_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X3))) )),
% 19.85/3.08    inference(forward_demodulation,[],[f1085,f107])).
% 19.85/3.08  fof(f1085,plain,(
% 19.85/3.08    ( ! [X4,X5,X3] : (k2_xboole_0(X4,k4_xboole_0(X5,k2_xboole_0(X3,X4))) = k2_xboole_0(X4,k4_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X3))) )),
% 19.85/3.08    inference(superposition,[],[f107,f34])).
% 19.85/3.08  fof(f32,plain,(
% 19.85/3.08    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl4_1),
% 19.85/3.08    inference(avatar_component_clause,[],[f31])).
% 19.85/3.08  fof(f31,plain,(
% 19.85/3.08    spl4_1 <=> k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 19.85/3.08    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 19.85/3.08  fof(f33,plain,(
% 19.85/3.08    ~spl4_1),
% 19.85/3.08    inference(avatar_split_clause,[],[f16,f31])).
% 19.85/3.08  fof(f16,plain,(
% 19.85/3.08    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 19.85/3.08    inference(cnf_transformation,[],[f10])).
% 19.85/3.08  fof(f10,plain,(
% 19.85/3.08    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 19.85/3.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 19.85/3.08  fof(f9,plain,(
% 19.85/3.08    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 19.85/3.08    introduced(choice_axiom,[])).
% 19.85/3.08  fof(f8,plain,(
% 19.85/3.08    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 19.85/3.08    inference(ennf_transformation,[],[f7])).
% 19.85/3.08  fof(f7,negated_conjecture,(
% 19.85/3.08    ~! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 19.85/3.08    inference(negated_conjecture,[],[f6])).
% 19.85/3.08  fof(f6,conjecture,(
% 19.85/3.08    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 19.85/3.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 19.85/3.08  % SZS output end Proof for theBenchmark
% 19.85/3.08  % (5377)------------------------------
% 19.85/3.08  % (5377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.85/3.08  % (5377)Termination reason: Refutation
% 19.85/3.08  
% 19.85/3.08  % (5377)Memory used [KB]: 97098
% 19.85/3.08  % (5377)Time elapsed: 2.652 s
% 19.85/3.08  % (5377)------------------------------
% 19.85/3.08  % (5377)------------------------------
% 19.85/3.09  % (5370)Success in time 2.719 s
%------------------------------------------------------------------------------
