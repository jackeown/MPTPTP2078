%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:31 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  169 ( 333 expanded)
%              Number of equality atoms :   33 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1775,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1756])).

fof(f1756,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f1671,f1712])).

fof(f1712,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1546,f1705])).

fof(f1705,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) ),
    inference(resolution,[],[f1700,f158])).

fof(f158,plain,(
    ! [X28,X29] :
      ( r2_hidden(X28,X29)
      | k1_xboole_0 = k4_xboole_0(k2_enumset1(X28,X28,X28,X28),k4_xboole_0(k2_enumset1(X28,X28,X28,X28),X29)) ) ),
    inference(resolution,[],[f60,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1700,plain,(
    ! [X0] : ~ r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) ),
    inference(resolution,[],[f249,f32])).

fof(f32,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f249,plain,(
    ! [X59,X58] :
      ( ~ r2_hidden(X59,sK2)
      | ~ r2_hidden(X59,k4_xboole_0(X58,k4_xboole_0(X58,sK1))) ) ),
    inference(superposition,[],[f78,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f39,f39])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f78,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k4_xboole_0(sK1,X3))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f73,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f73,plain,(
    ! [X1] : r1_xboole_0(k4_xboole_0(sK1,X1),sK2) ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k4_xboole_0(X0,X2),X1) ) ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1546,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f118,f56])).

fof(f118,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(resolution,[],[f58,f55])).

fof(f55,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f31,f39,f54])).

fof(f31,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1671,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f507,f61])).

fof(f507,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f498,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,X0)) ) ),
    inference(superposition,[],[f59,f56])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f498,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f203,f34])).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f203,plain,(
    ! [X19,X17,X18] :
      ( r1_xboole_0(k2_xboole_0(X18,X19),X17)
      | ~ r1_xboole_0(X17,X19)
      | ~ r1_xboole_0(X17,X18) ) ),
    inference(resolution,[],[f49,f45])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (805371906)
% 0.13/0.41  ipcrm: permission denied for id (805503010)
% 0.13/0.42  ipcrm: permission denied for id (805535792)
% 0.21/0.44  ipcrm: permission denied for id (805634109)
% 0.21/0.45  ipcrm: permission denied for id (805732424)
% 0.21/0.46  ipcrm: permission denied for id (805797972)
% 0.21/0.48  ipcrm: permission denied for id (805863518)
% 0.21/0.57  % (32459)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.82/0.59  % (32455)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.82/0.60  % (32449)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.82/0.61  % (32452)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.82/0.62  % (32448)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.82/0.63  % (32457)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.19/0.64  % (32458)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.23/0.65  % (32454)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.23/0.65  % (32447)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.23/0.65  % (32461)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.23/0.66  % (32450)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.23/0.66  % (32456)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.23/0.66  % (32448)Refutation found. Thanks to Tanya!
% 1.23/0.66  % SZS status Theorem for theBenchmark
% 1.23/0.67  % (32453)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.23/0.67  % SZS output start Proof for theBenchmark
% 1.23/0.67  fof(f1775,plain,(
% 1.23/0.67    $false),
% 1.23/0.67    inference(trivial_inequality_removal,[],[f1756])).
% 1.23/0.67  fof(f1756,plain,(
% 1.23/0.67    k1_xboole_0 != k1_xboole_0),
% 1.23/0.67    inference(superposition,[],[f1671,f1712])).
% 1.23/0.67  fof(f1712,plain,(
% 1.23/0.67    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.23/0.67    inference(backward_demodulation,[],[f1546,f1705])).
% 1.23/0.67  fof(f1705,plain,(
% 1.23/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK1))))) )),
% 1.23/0.67    inference(resolution,[],[f1700,f158])).
% 1.23/0.67  fof(f158,plain,(
% 1.23/0.67    ( ! [X28,X29] : (r2_hidden(X28,X29) | k1_xboole_0 = k4_xboole_0(k2_enumset1(X28,X28,X28,X28),k4_xboole_0(k2_enumset1(X28,X28,X28,X28),X29))) )),
% 1.23/0.67    inference(resolution,[],[f60,f57])).
% 1.23/0.67  fof(f57,plain,(
% 1.23/0.67    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.23/0.67    inference(definition_unfolding,[],[f43,f54])).
% 1.23/0.67  fof(f54,plain,(
% 1.23/0.67    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.23/0.67    inference(definition_unfolding,[],[f35,f53])).
% 1.23/0.67  fof(f53,plain,(
% 1.23/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.23/0.67    inference(definition_unfolding,[],[f38,f48])).
% 1.23/0.67  fof(f48,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f12])).
% 1.23/0.67  fof(f12,axiom,(
% 1.23/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.23/0.67  fof(f38,plain,(
% 1.23/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f11])).
% 1.23/0.67  fof(f11,axiom,(
% 1.23/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.23/0.67  fof(f35,plain,(
% 1.23/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f10])).
% 1.23/0.67  fof(f10,axiom,(
% 1.23/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.23/0.67  fof(f43,plain,(
% 1.23/0.67    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f20])).
% 1.23/0.67  fof(f20,plain,(
% 1.23/0.67    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.23/0.67    inference(ennf_transformation,[],[f13])).
% 1.23/0.67  fof(f13,axiom,(
% 1.23/0.67    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.23/0.67  fof(f60,plain,(
% 1.23/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.23/0.67    inference(definition_unfolding,[],[f46,f39])).
% 1.23/0.67  fof(f39,plain,(
% 1.23/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.23/0.67    inference(cnf_transformation,[],[f7])).
% 1.23/0.67  fof(f7,axiom,(
% 1.23/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.23/0.67  fof(f46,plain,(
% 1.23/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f30])).
% 1.23/0.67  fof(f30,plain,(
% 1.23/0.67    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.23/0.67    inference(nnf_transformation,[],[f2])).
% 1.23/0.67  fof(f2,axiom,(
% 1.23/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.23/0.67  fof(f1700,plain,(
% 1.23/0.67    ( ! [X0] : (~r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) )),
% 1.23/0.67    inference(resolution,[],[f249,f32])).
% 1.23/0.67  fof(f32,plain,(
% 1.23/0.67    r2_hidden(sK3,sK2)),
% 1.23/0.67    inference(cnf_transformation,[],[f27])).
% 1.23/0.67  fof(f27,plain,(
% 1.23/0.67    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.23/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f26])).
% 1.23/0.67  fof(f26,plain,(
% 1.23/0.67    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.23/0.67    introduced(choice_axiom,[])).
% 1.23/0.67  fof(f18,plain,(
% 1.23/0.67    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.23/0.67    inference(flattening,[],[f17])).
% 1.23/0.67  fof(f17,plain,(
% 1.23/0.67    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.23/0.67    inference(ennf_transformation,[],[f15])).
% 1.23/0.67  fof(f15,negated_conjecture,(
% 1.23/0.67    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.23/0.67    inference(negated_conjecture,[],[f14])).
% 1.23/0.67  fof(f14,conjecture,(
% 1.23/0.67    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.23/0.67  fof(f249,plain,(
% 1.23/0.67    ( ! [X59,X58] : (~r2_hidden(X59,sK2) | ~r2_hidden(X59,k4_xboole_0(X58,k4_xboole_0(X58,sK1)))) )),
% 1.23/0.67    inference(superposition,[],[f78,f56])).
% 1.23/0.67  fof(f56,plain,(
% 1.23/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.23/0.67    inference(definition_unfolding,[],[f37,f39,f39])).
% 1.23/0.67  fof(f37,plain,(
% 1.23/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f1])).
% 1.23/0.67  fof(f1,axiom,(
% 1.23/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.23/0.67  fof(f78,plain,(
% 1.23/0.67    ( ! [X2,X3] : (~r2_hidden(X2,k4_xboole_0(sK1,X3)) | ~r2_hidden(X2,sK2)) )),
% 1.23/0.67    inference(resolution,[],[f73,f42])).
% 1.23/0.67  fof(f42,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f29])).
% 1.23/0.67  fof(f29,plain,(
% 1.23/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.23/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).
% 1.23/0.67  fof(f28,plain,(
% 1.23/0.67    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.23/0.67    introduced(choice_axiom,[])).
% 1.23/0.67  fof(f19,plain,(
% 1.23/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.23/0.67    inference(ennf_transformation,[],[f16])).
% 1.23/0.67  fof(f16,plain,(
% 1.23/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.23/0.67    inference(rectify,[],[f4])).
% 1.23/0.67  fof(f4,axiom,(
% 1.23/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.23/0.67  fof(f73,plain,(
% 1.23/0.67    ( ! [X1] : (r1_xboole_0(k4_xboole_0(sK1,X1),sK2)) )),
% 1.23/0.67    inference(resolution,[],[f69,f61])).
% 1.23/0.67  fof(f61,plain,(
% 1.23/0.67    r1_xboole_0(sK1,sK2)),
% 1.23/0.67    inference(resolution,[],[f45,f33])).
% 1.23/0.67  fof(f33,plain,(
% 1.23/0.67    r1_xboole_0(sK2,sK1)),
% 1.23/0.67    inference(cnf_transformation,[],[f27])).
% 1.23/0.67  fof(f45,plain,(
% 1.23/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f22])).
% 1.23/0.67  fof(f22,plain,(
% 1.23/0.67    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.23/0.67    inference(ennf_transformation,[],[f3])).
% 1.23/0.67  fof(f3,axiom,(
% 1.23/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.23/0.67  fof(f69,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X0,X2),X1)) )),
% 1.23/0.67    inference(resolution,[],[f52,f36])).
% 1.23/0.67  fof(f36,plain,(
% 1.23/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f6])).
% 1.23/0.67  fof(f6,axiom,(
% 1.23/0.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.23/0.67  fof(f52,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f25])).
% 1.23/0.67  fof(f25,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.23/0.67    inference(flattening,[],[f24])).
% 1.23/0.67  fof(f24,plain,(
% 1.23/0.67    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.23/0.67    inference(ennf_transformation,[],[f8])).
% 1.23/0.67  fof(f8,axiom,(
% 1.23/0.67    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.23/0.67  fof(f1546,plain,(
% 1.23/0.67    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.23/0.67    inference(superposition,[],[f118,f56])).
% 1.23/0.67  fof(f118,plain,(
% 1.23/0.67    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 1.23/0.67    inference(resolution,[],[f58,f55])).
% 1.23/0.67  fof(f55,plain,(
% 1.23/0.67    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.23/0.67    inference(definition_unfolding,[],[f31,f39,f54])).
% 1.23/0.67  fof(f31,plain,(
% 1.23/0.67    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.23/0.67    inference(cnf_transformation,[],[f27])).
% 1.23/0.67  fof(f58,plain,(
% 1.23/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.23/0.67    inference(definition_unfolding,[],[f44,f39])).
% 1.23/0.67  fof(f44,plain,(
% 1.23/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f21])).
% 1.23/0.67  fof(f21,plain,(
% 1.23/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.23/0.67    inference(ennf_transformation,[],[f5])).
% 1.23/0.67  fof(f5,axiom,(
% 1.23/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.23/0.67  fof(f1671,plain,(
% 1.23/0.67    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.23/0.67    inference(resolution,[],[f507,f61])).
% 1.23/0.67  fof(f507,plain,(
% 1.23/0.67    ~r1_xboole_0(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.23/0.67    inference(resolution,[],[f498,f225])).
% 1.23/0.67  fof(f225,plain,(
% 1.23/0.67    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.23/0.67    inference(superposition,[],[f59,f56])).
% 1.23/0.67  fof(f59,plain,(
% 1.23/0.67    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.23/0.67    inference(definition_unfolding,[],[f47,f39])).
% 1.23/0.67  fof(f47,plain,(
% 1.23/0.67    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.23/0.67    inference(cnf_transformation,[],[f30])).
% 1.23/0.67  fof(f498,plain,(
% 1.23/0.67    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.23/0.67    inference(resolution,[],[f203,f34])).
% 1.23/0.67  fof(f34,plain,(
% 1.23/0.67    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.23/0.67    inference(cnf_transformation,[],[f27])).
% 1.23/0.67  fof(f203,plain,(
% 1.23/0.67    ( ! [X19,X17,X18] : (r1_xboole_0(k2_xboole_0(X18,X19),X17) | ~r1_xboole_0(X17,X19) | ~r1_xboole_0(X17,X18)) )),
% 1.23/0.67    inference(resolution,[],[f49,f45])).
% 1.23/0.67  fof(f49,plain,(
% 1.23/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.23/0.67    inference(cnf_transformation,[],[f23])).
% 1.23/0.67  fof(f23,plain,(
% 1.23/0.67    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.23/0.67    inference(ennf_transformation,[],[f9])).
% 1.23/0.67  fof(f9,axiom,(
% 1.23/0.67    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.23/0.67  % SZS output end Proof for theBenchmark
% 1.23/0.67  % (32448)------------------------------
% 1.23/0.67  % (32448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.67  % (32448)Termination reason: Refutation
% 1.23/0.67  
% 1.23/0.67  % (32448)Memory used [KB]: 2558
% 1.23/0.67  % (32448)Time elapsed: 0.081 s
% 1.23/0.67  % (32448)------------------------------
% 1.23/0.67  % (32448)------------------------------
% 1.23/0.67  % (32312)Success in time 0.31 s
%------------------------------------------------------------------------------
