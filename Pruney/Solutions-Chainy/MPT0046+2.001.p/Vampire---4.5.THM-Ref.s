%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:51 EST 2020

% Result     : Theorem 9.58s
% Output     : Refutation 9.58s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 172 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  201 ( 475 expanded)
%              Number of equality atoms :   61 ( 133 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43516,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f213,f43389,f43390])).

fof(f43390,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f43160])).

fof(f43160,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f212,f41216])).

fof(f41216,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f41172,f3044])).

fof(f3044,plain,(
    ! [X39,X41,X40] : k2_xboole_0(X39,k2_xboole_0(X41,k4_xboole_0(X39,X40))) = k2_xboole_0(X41,X39) ),
    inference(superposition,[],[f461,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f461,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f54,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f41172,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f40833,f48])).

fof(f40833,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f40332,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f40332,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f335,f11736])).

fof(f11736,plain,(
    ! [X54,X55,X53] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X55,k2_xboole_0(X53,X54)),X54) ),
    inference(forward_demodulation,[],[f11717,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f11717,plain,(
    ! [X54,X55,X53] : k3_xboole_0(k4_xboole_0(X55,k2_xboole_0(X53,X54)),X54) = k3_xboole_0(X54,k1_xboole_0) ),
    inference(superposition,[],[f2541,f11672])).

fof(f11672,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(subsumption_resolution,[],[f11648,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f11648,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))
      | r1_xboole_0(X0,k4_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f1427,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1427,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK2(X4,X5),k4_xboole_0(X6,X4))
      | k1_xboole_0 = k3_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f137,f49])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),k4_xboole_0(X2,X0)) ) ),
    inference(resolution,[],[f63,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f2541,plain,(
    ! [X12,X13,X11] : k3_xboole_0(X11,k3_xboole_0(k2_xboole_0(X12,X11),X13)) = k3_xboole_0(X13,X11) ),
    inference(superposition,[],[f296,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f42,f41])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f296,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f53,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f335,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f275,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f275,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f212,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f43389,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f43388])).

fof(f43388,plain,
    ( $false
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f43387])).

fof(f43387,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(superposition,[],[f212,f41216])).

fof(f213,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f36,f210])).

fof(f36,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:25:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (21191)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (21184)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (21199)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (21199)Refutation not found, incomplete strategy% (21199)------------------------------
% 0.21/0.47  % (21199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21191)Refutation not found, incomplete strategy% (21191)------------------------------
% 0.21/0.47  % (21191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21199)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  % (21191)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21199)Memory used [KB]: 10490
% 0.21/0.47  
% 0.21/0.47  % (21191)Memory used [KB]: 6012
% 0.21/0.47  % (21199)Time elapsed: 0.074 s
% 0.21/0.47  % (21199)------------------------------
% 0.21/0.47  % (21199)------------------------------
% 0.21/0.47  % (21191)Time elapsed: 0.004 s
% 0.21/0.47  % (21191)------------------------------
% 0.21/0.47  % (21191)------------------------------
% 0.21/0.50  % (21186)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (21182)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (21179)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (21193)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (21192)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (21192)Refutation not found, incomplete strategy% (21192)------------------------------
% 0.21/0.51  % (21192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21192)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21192)Memory used [KB]: 1663
% 0.21/0.51  % (21192)Time elapsed: 0.102 s
% 0.21/0.51  % (21192)------------------------------
% 0.21/0.51  % (21192)------------------------------
% 0.21/0.51  % (21185)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (21180)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21194)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (21181)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (21194)Refutation not found, incomplete strategy% (21194)------------------------------
% 0.21/0.51  % (21194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21194)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21194)Memory used [KB]: 6140
% 0.21/0.51  % (21194)Time elapsed: 0.101 s
% 0.21/0.51  % (21194)------------------------------
% 0.21/0.51  % (21194)------------------------------
% 0.21/0.51  % (21197)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (21179)Refutation not found, incomplete strategy% (21179)------------------------------
% 0.21/0.51  % (21179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21179)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21179)Memory used [KB]: 6140
% 0.21/0.51  % (21179)Time elapsed: 0.096 s
% 0.21/0.51  % (21179)------------------------------
% 0.21/0.51  % (21179)------------------------------
% 0.21/0.52  % (21183)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (21189)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (21189)Refutation not found, incomplete strategy% (21189)------------------------------
% 0.21/0.52  % (21189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21189)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21189)Memory used [KB]: 6012
% 0.21/0.52  % (21189)Time elapsed: 0.106 s
% 0.21/0.52  % (21189)------------------------------
% 0.21/0.52  % (21189)------------------------------
% 0.21/0.52  % (21182)Refutation not found, incomplete strategy% (21182)------------------------------
% 0.21/0.52  % (21182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21182)Memory used [KB]: 10618
% 0.21/0.52  % (21182)Time elapsed: 0.112 s
% 0.21/0.52  % (21182)------------------------------
% 0.21/0.52  % (21182)------------------------------
% 0.21/0.52  % (21188)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (21195)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (21190)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (21198)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (21190)Refutation not found, incomplete strategy% (21190)------------------------------
% 0.21/0.53  % (21190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21190)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21190)Memory used [KB]: 10618
% 0.21/0.53  % (21190)Time elapsed: 0.104 s
% 0.21/0.53  % (21190)------------------------------
% 0.21/0.53  % (21190)------------------------------
% 0.21/0.53  % (21196)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (21180)Refutation not found, incomplete strategy% (21180)------------------------------
% 0.21/0.53  % (21180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21180)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21180)Memory used [KB]: 10618
% 0.21/0.53  % (21180)Time elapsed: 0.108 s
% 0.21/0.53  % (21180)------------------------------
% 0.21/0.53  % (21180)------------------------------
% 0.21/0.53  % (21187)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 4.77/0.95  % (21184)Time limit reached!
% 4.77/0.95  % (21184)------------------------------
% 4.77/0.95  % (21184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/0.95  % (21184)Termination reason: Time limit
% 4.77/0.95  % (21184)Termination phase: Saturation
% 4.77/0.95  
% 4.77/0.95  % (21184)Memory used [KB]: 10874
% 4.77/0.95  % (21184)Time elapsed: 0.500 s
% 4.77/0.95  % (21184)------------------------------
% 4.77/0.95  % (21184)------------------------------
% 4.77/1.02  % (21187)Time limit reached!
% 4.77/1.02  % (21187)------------------------------
% 4.77/1.02  % (21187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.02  % (21187)Termination reason: Time limit
% 4.77/1.02  % (21187)Termination phase: Saturation
% 4.77/1.02  
% 4.77/1.02  % (21187)Memory used [KB]: 19317
% 4.77/1.02  % (21187)Time elapsed: 0.600 s
% 4.77/1.02  % (21187)------------------------------
% 4.77/1.02  % (21187)------------------------------
% 7.78/1.34  % (21188)Time limit reached!
% 7.78/1.34  % (21188)------------------------------
% 7.78/1.34  % (21188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.78/1.34  % (21188)Termination reason: Time limit
% 7.78/1.34  % (21188)Termination phase: Saturation
% 7.78/1.34  
% 7.78/1.34  % (21188)Memory used [KB]: 32494
% 7.78/1.34  % (21188)Time elapsed: 0.900 s
% 7.78/1.34  % (21188)------------------------------
% 7.78/1.34  % (21188)------------------------------
% 9.36/1.52  % (21181)Time limit reached!
% 9.36/1.52  % (21181)------------------------------
% 9.36/1.52  % (21181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.36/1.52  % (21181)Termination reason: Time limit
% 9.36/1.52  
% 9.36/1.52  % (21181)Memory used [KB]: 24818
% 9.36/1.52  % (21181)Time elapsed: 1.114 s
% 9.36/1.52  % (21181)------------------------------
% 9.36/1.52  % (21181)------------------------------
% 9.58/1.55  % (21186)Refutation found. Thanks to Tanya!
% 9.58/1.55  % SZS status Theorem for theBenchmark
% 9.58/1.55  % SZS output start Proof for theBenchmark
% 9.58/1.55  fof(f43516,plain,(
% 9.58/1.55    $false),
% 9.58/1.55    inference(avatar_sat_refutation,[],[f213,f43389,f43390])).
% 9.58/1.55  fof(f43390,plain,(
% 9.58/1.55    spl4_1),
% 9.58/1.55    inference(avatar_contradiction_clause,[],[f43160])).
% 9.58/1.55  fof(f43160,plain,(
% 9.58/1.55    $false | spl4_1),
% 9.58/1.55    inference(unit_resulting_resolution,[],[f212,f41216])).
% 9.58/1.55  fof(f41216,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.58/1.55    inference(forward_demodulation,[],[f41172,f3044])).
% 9.58/1.55  fof(f3044,plain,(
% 9.58/1.55    ( ! [X39,X41,X40] : (k2_xboole_0(X39,k2_xboole_0(X41,k4_xboole_0(X39,X40))) = k2_xboole_0(X41,X39)) )),
% 9.58/1.55    inference(superposition,[],[f461,f89])).
% 9.58/1.55  fof(f89,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 9.58/1.55    inference(unit_resulting_resolution,[],[f39,f48])).
% 9.58/1.55  fof(f48,plain,(
% 9.58/1.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 9.58/1.55    inference(cnf_transformation,[],[f23])).
% 9.58/1.55  fof(f23,plain,(
% 9.58/1.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 9.58/1.55    inference(ennf_transformation,[],[f7])).
% 9.58/1.55  fof(f7,axiom,(
% 9.58/1.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 9.58/1.55  fof(f39,plain,(
% 9.58/1.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 9.58/1.55    inference(cnf_transformation,[],[f13])).
% 9.58/1.55  fof(f13,axiom,(
% 9.58/1.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 9.58/1.55  fof(f461,plain,(
% 9.58/1.55    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 9.58/1.55    inference(superposition,[],[f54,f41])).
% 9.58/1.55  fof(f41,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 9.58/1.55    inference(cnf_transformation,[],[f1])).
% 9.58/1.55  fof(f1,axiom,(
% 9.58/1.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 9.58/1.55  fof(f54,plain,(
% 9.58/1.55    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 9.58/1.55    inference(cnf_transformation,[],[f14])).
% 9.58/1.55  fof(f14,axiom,(
% 9.58/1.55    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 9.58/1.55  fof(f41172,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 9.58/1.55    inference(unit_resulting_resolution,[],[f40833,f48])).
% 9.58/1.55  fof(f40833,plain,(
% 9.58/1.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 9.58/1.55    inference(unit_resulting_resolution,[],[f40332,f51])).
% 9.58/1.55  fof(f51,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 9.58/1.55    inference(cnf_transformation,[],[f30])).
% 9.58/1.55  fof(f30,plain,(
% 9.58/1.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 9.58/1.55    inference(nnf_transformation,[],[f6])).
% 9.58/1.55  fof(f6,axiom,(
% 9.58/1.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 9.58/1.55  fof(f40332,plain,(
% 9.58/1.55    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4)))) )),
% 9.58/1.55    inference(superposition,[],[f335,f11736])).
% 9.58/1.55  fof(f11736,plain,(
% 9.58/1.55    ( ! [X54,X55,X53] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X55,k2_xboole_0(X53,X54)),X54)) )),
% 9.58/1.55    inference(forward_demodulation,[],[f11717,f37])).
% 9.58/1.55  fof(f37,plain,(
% 9.58/1.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 9.58/1.55    inference(cnf_transformation,[],[f11])).
% 9.58/1.55  fof(f11,axiom,(
% 9.58/1.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 9.58/1.55  fof(f11717,plain,(
% 9.58/1.55    ( ! [X54,X55,X53] : (k3_xboole_0(k4_xboole_0(X55,k2_xboole_0(X53,X54)),X54) = k3_xboole_0(X54,k1_xboole_0)) )),
% 9.58/1.55    inference(superposition,[],[f2541,f11672])).
% 9.58/1.55  fof(f11672,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.58/1.55    inference(subsumption_resolution,[],[f11648,f49])).
% 9.58/1.55  fof(f49,plain,(
% 9.58/1.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 9.58/1.55    inference(cnf_transformation,[],[f29])).
% 9.58/1.55  fof(f29,plain,(
% 9.58/1.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 9.58/1.55    inference(nnf_transformation,[],[f4])).
% 9.58/1.55  fof(f4,axiom,(
% 9.58/1.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 9.58/1.55  fof(f11648,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) | r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.58/1.55    inference(resolution,[],[f1427,f45])).
% 9.58/1.55  fof(f45,plain,(
% 9.58/1.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 9.58/1.55    inference(cnf_transformation,[],[f28])).
% 9.58/1.55  fof(f28,plain,(
% 9.58/1.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 9.58/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f27])).
% 9.58/1.55  fof(f27,plain,(
% 9.58/1.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 9.58/1.55    introduced(choice_axiom,[])).
% 9.58/1.55  fof(f21,plain,(
% 9.58/1.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 9.58/1.55    inference(ennf_transformation,[],[f19])).
% 9.58/1.55  fof(f19,plain,(
% 9.58/1.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 9.58/1.55    inference(rectify,[],[f5])).
% 9.58/1.55  fof(f5,axiom,(
% 9.58/1.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 9.58/1.55  fof(f1427,plain,(
% 9.58/1.55    ( ! [X6,X4,X5] : (~r2_hidden(sK2(X4,X5),k4_xboole_0(X6,X4)) | k1_xboole_0 = k3_xboole_0(X4,X5)) )),
% 9.58/1.55    inference(resolution,[],[f137,f49])).
% 9.58/1.55  fof(f137,plain,(
% 9.58/1.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r2_hidden(sK2(X0,X1),k4_xboole_0(X2,X0))) )),
% 9.58/1.55    inference(resolution,[],[f63,f44])).
% 9.58/1.55  fof(f44,plain,(
% 9.58/1.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 9.58/1.55    inference(cnf_transformation,[],[f28])).
% 9.58/1.55  fof(f63,plain,(
% 9.58/1.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 9.58/1.55    inference(equality_resolution,[],[f57])).
% 9.58/1.55  fof(f57,plain,(
% 9.58/1.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 9.58/1.55    inference(cnf_transformation,[],[f35])).
% 9.58/1.55  fof(f35,plain,(
% 9.58/1.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.58/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 9.58/1.55  fof(f34,plain,(
% 9.58/1.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 9.58/1.55    introduced(choice_axiom,[])).
% 9.58/1.55  fof(f33,plain,(
% 9.58/1.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.58/1.55    inference(rectify,[],[f32])).
% 9.58/1.55  fof(f32,plain,(
% 9.58/1.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.58/1.55    inference(flattening,[],[f31])).
% 9.58/1.55  fof(f31,plain,(
% 9.58/1.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.58/1.55    inference(nnf_transformation,[],[f3])).
% 9.58/1.55  fof(f3,axiom,(
% 9.58/1.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 9.58/1.55  fof(f2541,plain,(
% 9.58/1.55    ( ! [X12,X13,X11] : (k3_xboole_0(X11,k3_xboole_0(k2_xboole_0(X12,X11),X13)) = k3_xboole_0(X13,X11)) )),
% 9.58/1.55    inference(superposition,[],[f296,f77])).
% 9.58/1.55  fof(f77,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 9.58/1.55    inference(superposition,[],[f42,f41])).
% 9.58/1.55  fof(f42,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 9.58/1.55    inference(cnf_transformation,[],[f9])).
% 9.58/1.55  fof(f9,axiom,(
% 9.58/1.55    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 9.58/1.55  fof(f296,plain,(
% 9.58/1.55    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 9.58/1.55    inference(superposition,[],[f53,f40])).
% 9.58/1.55  fof(f40,plain,(
% 9.58/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.58/1.55    inference(cnf_transformation,[],[f2])).
% 9.58/1.55  fof(f2,axiom,(
% 9.58/1.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.58/1.55  fof(f53,plain,(
% 9.58/1.55    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 9.58/1.55    inference(cnf_transformation,[],[f8])).
% 9.58/1.55  fof(f8,axiom,(
% 9.58/1.55    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 9.58/1.55  fof(f335,plain,(
% 9.58/1.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 9.58/1.55    inference(unit_resulting_resolution,[],[f275,f47])).
% 9.58/1.55  fof(f47,plain,(
% 9.58/1.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 9.58/1.55    inference(cnf_transformation,[],[f22])).
% 9.58/1.55  fof(f22,plain,(
% 9.58/1.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 9.58/1.55    inference(ennf_transformation,[],[f10])).
% 9.58/1.55  fof(f10,axiom,(
% 9.58/1.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 9.58/1.55  fof(f275,plain,(
% 9.58/1.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 9.58/1.55    inference(unit_resulting_resolution,[],[f38,f55])).
% 9.58/1.55  fof(f55,plain,(
% 9.58/1.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 9.58/1.55    inference(cnf_transformation,[],[f24])).
% 9.58/1.55  fof(f24,plain,(
% 9.58/1.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 9.58/1.55    inference(ennf_transformation,[],[f12])).
% 9.58/1.55  fof(f12,axiom,(
% 9.58/1.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 9.58/1.55  fof(f38,plain,(
% 9.58/1.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 9.58/1.55    inference(cnf_transformation,[],[f16])).
% 9.58/1.55  fof(f16,axiom,(
% 9.58/1.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 9.58/1.55  fof(f212,plain,(
% 9.58/1.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | spl4_1),
% 9.58/1.55    inference(avatar_component_clause,[],[f210])).
% 9.58/1.55  fof(f210,plain,(
% 9.58/1.55    spl4_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 9.58/1.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 9.58/1.55  fof(f43389,plain,(
% 9.58/1.55    spl4_1),
% 9.58/1.55    inference(avatar_contradiction_clause,[],[f43388])).
% 9.58/1.55  fof(f43388,plain,(
% 9.58/1.55    $false | spl4_1),
% 9.58/1.55    inference(trivial_inequality_removal,[],[f43387])).
% 9.58/1.55  fof(f43387,plain,(
% 9.58/1.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) | spl4_1),
% 9.58/1.55    inference(superposition,[],[f212,f41216])).
% 9.58/1.55  fof(f213,plain,(
% 9.58/1.55    ~spl4_1),
% 9.58/1.55    inference(avatar_split_clause,[],[f36,f210])).
% 9.58/1.55  fof(f36,plain,(
% 9.58/1.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 9.58/1.55    inference(cnf_transformation,[],[f26])).
% 9.58/1.55  fof(f26,plain,(
% 9.58/1.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 9.58/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).
% 9.58/1.55  fof(f25,plain,(
% 9.58/1.55    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 9.58/1.55    introduced(choice_axiom,[])).
% 9.58/1.55  fof(f20,plain,(
% 9.58/1.55    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 9.58/1.55    inference(ennf_transformation,[],[f18])).
% 9.58/1.55  fof(f18,negated_conjecture,(
% 9.58/1.55    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 9.58/1.55    inference(negated_conjecture,[],[f17])).
% 9.58/1.55  fof(f17,conjecture,(
% 9.58/1.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 9.58/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 9.58/1.55  % SZS output end Proof for theBenchmark
% 9.58/1.55  % (21186)------------------------------
% 9.58/1.55  % (21186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.58/1.55  % (21186)Termination reason: Refutation
% 9.58/1.55  
% 9.58/1.55  % (21186)Memory used [KB]: 26737
% 9.58/1.55  % (21186)Time elapsed: 1.139 s
% 9.58/1.55  % (21186)------------------------------
% 9.58/1.55  % (21186)------------------------------
% 9.58/1.56  % (21178)Success in time 1.198 s
%------------------------------------------------------------------------------
