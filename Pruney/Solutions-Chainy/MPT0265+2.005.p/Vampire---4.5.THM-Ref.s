%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:26 EST 2020

% Result     : Theorem 32.13s
% Output     : Refutation 32.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 518 expanded)
%              Number of leaves         :    7 ( 145 expanded)
%              Depth                    :   21
%              Number of atoms          :  149 (1114 expanded)
%              Number of equality atoms :   67 ( 680 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78483,plain,(
    $false ),
    inference(subsumption_resolution,[],[f78482,f58])).

fof(f58,plain,(
    ! [X4,X2,X0] : sP7(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP7(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f78482,plain,(
    ~ sP7(sK0,sK2,sK0,sK0) ),
    inference(forward_demodulation,[],[f78481,f77869])).

fof(f77869,plain,(
    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f63328,f63312])).

fof(f63312,plain,
    ( sK0 != sK2
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(equality_factoring,[],[f8915])).

fof(f8915,plain,
    ( sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f8907])).

fof(f8907,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f1870,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ sP7(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1870,plain,
    ( sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0)
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f574,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f574,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0) ),
    inference(resolution,[],[f254,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( sP7(X4,X2,X1,X0)
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP7(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP7(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f254,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f125,f17])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f125,plain,
    ( sP4(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
      | sP4(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
      | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0) ) ),
    inference(superposition,[],[f41,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK3(X0,X1,X2),X1,X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1) ),
    inference(definition_unfolding,[],[f15,f40,f39])).

fof(f15,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f63328,plain,
    ( sK0 = sK2
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f62832,f13])).

fof(f13,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK0 = sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f62832,plain,
    ( r2_hidden(sK2,sK1)
    | sK0 = sK2
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f505,f8915])).

fof(f505,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f255,f52])).

fof(f255,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    inference(resolution,[],[f125,f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f78481,plain,(
    ~ sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0) ),
    inference(subsumption_resolution,[],[f78480,f14])).

fof(f14,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f78480,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0) ),
    inference(forward_demodulation,[],[f78479,f77869])).

fof(f78479,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0) ),
    inference(subsumption_resolution,[],[f77929,f54])).

fof(f54,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f77929,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0) ),
    inference(backward_demodulation,[],[f973,f77869])).

fof(f973,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0) ),
    inference(resolution,[],[f277,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f277,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    inference(resolution,[],[f130,f16])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f130,plain,
    ( ~ sP4(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X1] :
      ( k2_enumset1(sK0,sK0,sK0,sK0) != X1
      | ~ sP4(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X1),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
      | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X1),X1) ) ),
    inference(superposition,[],[f41,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(sK3(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (21761)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.49  % (21748)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (21753)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (21753)Refutation not found, incomplete strategy% (21753)------------------------------
% 0.21/0.50  % (21753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21753)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21753)Memory used [KB]: 1663
% 0.21/0.50  % (21753)Time elapsed: 0.057 s
% 0.21/0.50  % (21753)------------------------------
% 0.21/0.50  % (21753)------------------------------
% 0.21/0.50  % (21764)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.50  % (21745)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21750)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (21756)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (21744)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (21749)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (21747)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (21742)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (21743)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (21756)Refutation not found, incomplete strategy% (21756)------------------------------
% 0.21/0.52  % (21756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21759)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (21756)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21756)Memory used [KB]: 1663
% 0.21/0.52  % (21756)Time elapsed: 0.106 s
% 0.21/0.52  % (21756)------------------------------
% 0.21/0.52  % (21756)------------------------------
% 0.21/0.52  % (21739)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (21740)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (21767)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (21757)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (21741)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (21767)Refutation not found, incomplete strategy% (21767)------------------------------
% 0.21/0.53  % (21767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21767)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21767)Memory used [KB]: 10746
% 0.21/0.53  % (21767)Time elapsed: 0.131 s
% 0.21/0.53  % (21767)------------------------------
% 0.21/0.53  % (21767)------------------------------
% 0.21/0.53  % (21768)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (21751)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (21762)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (21754)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (21760)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (21765)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (21766)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (21755)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (21746)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (21755)Refutation not found, incomplete strategy% (21755)------------------------------
% 0.21/0.55  % (21755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21755)Memory used [KB]: 10618
% 0.21/0.55  % (21755)Time elapsed: 0.142 s
% 0.21/0.55  % (21755)------------------------------
% 0.21/0.55  % (21755)------------------------------
% 0.21/0.55  % (21752)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (21758)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (21763)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.09/0.65  % (21769)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.09/0.66  % (21770)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.09/0.67  % (21771)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.09/0.68  % (21742)Refutation not found, incomplete strategy% (21742)------------------------------
% 2.09/0.68  % (21742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.68  % (21742)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.68  
% 2.09/0.68  % (21742)Memory used [KB]: 6140
% 2.09/0.68  % (21742)Time elapsed: 0.251 s
% 2.09/0.68  % (21742)------------------------------
% 2.09/0.68  % (21742)------------------------------
% 2.75/0.72  % (21772)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.32/0.80  % (21763)Time limit reached!
% 3.32/0.80  % (21763)------------------------------
% 3.32/0.80  % (21763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.80  % (21763)Termination reason: Time limit
% 3.32/0.80  % (21763)Termination phase: Saturation
% 3.32/0.80  
% 3.32/0.80  % (21763)Memory used [KB]: 12537
% 3.32/0.80  % (21763)Time elapsed: 0.400 s
% 3.32/0.80  % (21763)------------------------------
% 3.32/0.80  % (21763)------------------------------
% 3.32/0.81  % (21741)Time limit reached!
% 3.32/0.81  % (21741)------------------------------
% 3.32/0.81  % (21741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.81  % (21741)Termination reason: Time limit
% 3.32/0.81  
% 3.32/0.81  % (21741)Memory used [KB]: 6524
% 3.32/0.81  % (21741)Time elapsed: 0.410 s
% 3.32/0.81  % (21741)------------------------------
% 3.32/0.81  % (21741)------------------------------
% 3.32/0.84  % (21773)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.32/0.84  % (21773)Refutation not found, incomplete strategy% (21773)------------------------------
% 3.32/0.84  % (21773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.84  % (21773)Termination reason: Refutation not found, incomplete strategy
% 3.32/0.84  
% 3.32/0.84  % (21773)Memory used [KB]: 10618
% 3.32/0.84  % (21773)Time elapsed: 0.128 s
% 3.32/0.84  % (21773)------------------------------
% 3.32/0.84  % (21773)------------------------------
% 4.33/0.92  % (21768)Time limit reached!
% 4.33/0.92  % (21768)------------------------------
% 4.33/0.92  % (21768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.92  % (21768)Termination reason: Time limit
% 4.33/0.92  
% 4.33/0.92  % (21768)Memory used [KB]: 5117
% 4.33/0.92  % (21768)Time elapsed: 0.521 s
% 4.33/0.92  % (21768)------------------------------
% 4.33/0.92  % (21768)------------------------------
% 4.39/0.94  % (21774)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.39/0.95  % (21775)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.39/0.95  % (21745)Time limit reached!
% 4.39/0.95  % (21745)------------------------------
% 4.39/0.95  % (21745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.95  % (21745)Termination reason: Time limit
% 4.39/0.95  
% 4.39/0.95  % (21745)Memory used [KB]: 14583
% 4.39/0.95  % (21745)Time elapsed: 0.508 s
% 4.39/0.95  % (21745)------------------------------
% 4.39/0.95  % (21745)------------------------------
% 4.39/0.98  % (21776)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.98/1.02  % (21746)Time limit reached!
% 4.98/1.02  % (21746)------------------------------
% 4.98/1.02  % (21746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.98/1.02  % (21746)Termination reason: Time limit
% 4.98/1.02  
% 4.98/1.02  % (21746)Memory used [KB]: 5245
% 4.98/1.02  % (21746)Time elapsed: 0.622 s
% 4.98/1.02  % (21746)------------------------------
% 4.98/1.02  % (21746)------------------------------
% 4.98/1.06  % (21777)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.49/1.08  % (21778)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 5.49/1.09  % (21778)Refutation not found, incomplete strategy% (21778)------------------------------
% 5.49/1.09  % (21778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.49/1.09  % (21778)Termination reason: Refutation not found, incomplete strategy
% 5.49/1.09  
% 5.49/1.09  % (21778)Memory used [KB]: 10746
% 5.49/1.09  % (21778)Time elapsed: 0.100 s
% 5.49/1.09  % (21778)------------------------------
% 5.49/1.09  % (21778)------------------------------
% 5.49/1.16  % (21779)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 6.61/1.22  % (21780)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 6.87/1.22  % (21740)Time limit reached!
% 6.87/1.22  % (21740)------------------------------
% 6.87/1.22  % (21740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.87/1.22  % (21740)Termination reason: Time limit
% 6.87/1.22  
% 6.87/1.22  % (21740)Memory used [KB]: 3965
% 6.87/1.22  % (21740)Time elapsed: 0.817 s
% 6.87/1.22  % (21740)------------------------------
% 6.87/1.22  % (21740)------------------------------
% 7.64/1.37  % (21781)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 7.64/1.37  % (21771)Time limit reached!
% 7.64/1.37  % (21771)------------------------------
% 7.64/1.37  % (21771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.64/1.37  % (21771)Termination reason: Time limit
% 7.64/1.37  
% 7.64/1.37  % (21771)Memory used [KB]: 10874
% 7.64/1.37  % (21771)Time elapsed: 0.812 s
% 7.64/1.37  % (21771)------------------------------
% 7.64/1.37  % (21771)------------------------------
% 8.18/1.40  % (21766)Time limit reached!
% 8.18/1.40  % (21766)------------------------------
% 8.18/1.40  % (21766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.18/1.40  % (21766)Termination reason: Time limit
% 8.18/1.40  
% 8.18/1.40  % (21766)Memory used [KB]: 14328
% 8.18/1.40  % (21766)Time elapsed: 1.003 s
% 8.18/1.40  % (21766)------------------------------
% 8.18/1.40  % (21766)------------------------------
% 8.18/1.43  % (21751)Time limit reached!
% 8.18/1.43  % (21751)------------------------------
% 8.18/1.43  % (21751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.18/1.43  % (21751)Termination reason: Time limit
% 8.18/1.43  
% 8.18/1.43  % (21751)Memory used [KB]: 16119
% 8.18/1.43  % (21751)Time elapsed: 1.036 s
% 8.18/1.43  % (21751)------------------------------
% 8.18/1.43  % (21751)------------------------------
% 8.18/1.46  % (21775)Time limit reached!
% 8.18/1.46  % (21775)------------------------------
% 8.18/1.46  % (21775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.18/1.46  % (21775)Termination reason: Time limit
% 8.18/1.46  % (21775)Termination phase: Saturation
% 8.18/1.46  
% 8.18/1.46  % (21775)Memory used [KB]: 17654
% 8.18/1.46  % (21775)Time elapsed: 0.600 s
% 8.18/1.46  % (21775)------------------------------
% 8.18/1.46  % (21775)------------------------------
% 8.75/1.49  % (21782)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.37/1.58  % (21784)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 9.37/1.59  % (21783)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 9.37/1.59  % (21785)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 9.60/1.62  % (21739)Time limit reached!
% 9.60/1.62  % (21739)------------------------------
% 9.60/1.62  % (21739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.60/1.62  % (21739)Termination reason: Time limit
% 9.60/1.62  % (21739)Termination phase: Saturation
% 9.60/1.62  
% 9.60/1.62  % (21739)Memory used [KB]: 9722
% 9.60/1.62  % (21739)Time elapsed: 1.200 s
% 9.60/1.62  % (21739)------------------------------
% 9.60/1.62  % (21739)------------------------------
% 9.76/1.71  % (21744)Time limit reached!
% 9.76/1.71  % (21744)------------------------------
% 9.76/1.71  % (21744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.76/1.71  % (21744)Termination reason: Time limit
% 9.76/1.71  % (21744)Termination phase: Saturation
% 9.76/1.71  
% 9.76/1.71  % (21744)Memory used [KB]: 8699
% 9.76/1.71  % (21744)Time elapsed: 1.300 s
% 9.76/1.71  % (21744)------------------------------
% 9.76/1.71  % (21744)------------------------------
% 10.41/1.78  % (21786)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 10.41/1.79  % (21783)Refutation not found, incomplete strategy% (21783)------------------------------
% 10.41/1.79  % (21783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.41/1.79  % (21783)Termination reason: Refutation not found, incomplete strategy
% 10.41/1.79  
% 10.41/1.79  % (21783)Memory used [KB]: 6268
% 10.41/1.79  % (21783)Time elapsed: 0.293 s
% 10.41/1.79  % (21783)------------------------------
% 10.41/1.79  % (21783)------------------------------
% 10.97/1.82  % (21782)Time limit reached!
% 10.97/1.82  % (21782)------------------------------
% 10.97/1.82  % (21782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.97/1.82  % (21782)Termination reason: Time limit
% 10.97/1.82  % (21782)Termination phase: Saturation
% 10.97/1.82  
% 10.97/1.82  % (21782)Memory used [KB]: 14711
% 10.97/1.82  % (21782)Time elapsed: 0.400 s
% 10.97/1.82  % (21782)------------------------------
% 10.97/1.82  % (21782)------------------------------
% 10.97/1.84  % (21787)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 12.06/1.88  % (21784)Time limit reached!
% 12.06/1.88  % (21784)------------------------------
% 12.06/1.88  % (21784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.06/1.88  % (21784)Termination reason: Time limit
% 12.06/1.88  
% 12.06/1.88  % (21784)Memory used [KB]: 8059
% 12.06/1.88  % (21784)Time elapsed: 0.424 s
% 12.06/1.88  % (21784)------------------------------
% 12.06/1.88  % (21784)------------------------------
% 12.06/1.94  % (21788)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 12.06/1.95  % (21789)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 13.09/2.01  % (21785)Time limit reached!
% 13.09/2.01  % (21785)------------------------------
% 13.09/2.01  % (21785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.09/2.01  % (21785)Termination reason: Time limit
% 13.09/2.01  
% 13.09/2.01  % (21785)Memory used [KB]: 11897
% 13.09/2.01  % (21785)Time elapsed: 0.522 s
% 13.09/2.01  % (21785)------------------------------
% 13.09/2.01  % (21785)------------------------------
% 13.09/2.02  % (21765)Time limit reached!
% 13.09/2.02  % (21765)------------------------------
% 13.09/2.02  % (21765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.09/2.02  % (21765)Termination reason: Time limit
% 13.09/2.02  % (21765)Termination phase: Saturation
% 13.09/2.02  
% 13.09/2.02  % (21765)Memory used [KB]: 17014
% 13.09/2.02  % (21765)Time elapsed: 1.600 s
% 13.09/2.02  % (21765)------------------------------
% 13.09/2.02  % (21765)------------------------------
% 13.92/2.12  % (21786)Time limit reached!
% 13.92/2.12  % (21786)------------------------------
% 13.92/2.12  % (21786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.92/2.14  % (21786)Termination reason: Time limit
% 13.92/2.14  
% 13.92/2.14  % (21786)Memory used [KB]: 7675
% 13.92/2.14  % (21786)Time elapsed: 0.433 s
% 13.92/2.14  % (21786)------------------------------
% 13.92/2.14  % (21786)------------------------------
% 14.54/2.23  % (21788)Time limit reached!
% 14.54/2.23  % (21788)------------------------------
% 14.54/2.23  % (21788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.54/2.23  % (21788)Termination reason: Time limit
% 14.54/2.23  % (21788)Termination phase: Saturation
% 14.54/2.23  
% 14.54/2.23  % (21788)Memory used [KB]: 3454
% 14.54/2.23  % (21788)Time elapsed: 0.421 s
% 14.54/2.23  % (21788)------------------------------
% 14.54/2.23  % (21788)------------------------------
% 14.54/2.26  % (21759)Time limit reached!
% 14.54/2.26  % (21759)------------------------------
% 14.54/2.26  % (21759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.54/2.26  % (21789)Time limit reached!
% 14.54/2.26  % (21789)------------------------------
% 14.54/2.26  % (21789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.20/2.27  % (21789)Termination reason: Time limit
% 15.20/2.27  
% 15.20/2.27  % (21789)Memory used [KB]: 7931
% 15.20/2.27  % (21789)Time elapsed: 0.418 s
% 15.20/2.27  % (21789)------------------------------
% 15.20/2.27  % (21789)------------------------------
% 15.20/2.28  % (21759)Termination reason: Time limit
% 15.20/2.28  
% 15.20/2.28  % (21759)Memory used [KB]: 21364
% 15.20/2.28  % (21759)Time elapsed: 1.832 s
% 15.20/2.28  % (21759)------------------------------
% 15.20/2.28  % (21759)------------------------------
% 19.38/2.80  % (21754)Time limit reached!
% 19.38/2.80  % (21754)------------------------------
% 19.38/2.80  % (21754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.38/2.81  % (21754)Termination reason: Time limit
% 19.38/2.81  
% 19.38/2.81  % (21754)Memory used [KB]: 17526
% 19.38/2.81  % (21754)Time elapsed: 2.405 s
% 19.38/2.81  % (21754)------------------------------
% 19.38/2.81  % (21754)------------------------------
% 25.06/3.51  % (21750)Time limit reached!
% 25.06/3.51  % (21750)------------------------------
% 25.06/3.51  % (21750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.21/3.53  % (21750)Termination reason: Time limit
% 25.21/3.53  % (21750)Termination phase: Saturation
% 25.21/3.53  
% 25.21/3.53  % (21750)Memory used [KB]: 37739
% 25.21/3.53  % (21750)Time elapsed: 3.100 s
% 25.21/3.53  % (21750)------------------------------
% 25.21/3.53  % (21750)------------------------------
% 25.21/3.54  % (21747)Time limit reached!
% 25.21/3.54  % (21747)------------------------------
% 25.21/3.54  % (21747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.21/3.54  % (21747)Termination reason: Time limit
% 25.21/3.54  % (21747)Termination phase: Saturation
% 25.21/3.54  
% 25.21/3.54  % (21747)Memory used [KB]: 25202
% 25.21/3.54  % (21747)Time elapsed: 3.100 s
% 25.21/3.54  % (21747)------------------------------
% 25.21/3.54  % (21747)------------------------------
% 26.71/3.75  % (21758)Time limit reached!
% 26.71/3.75  % (21758)------------------------------
% 26.71/3.75  % (21758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.71/3.75  % (21758)Termination reason: Time limit
% 26.71/3.75  
% 26.71/3.75  % (21758)Memory used [KB]: 23539
% 26.71/3.75  % (21758)Time elapsed: 3.326 s
% 26.71/3.75  % (21758)------------------------------
% 26.71/3.75  % (21758)------------------------------
% 28.42/3.98  % (21777)Time limit reached!
% 28.42/3.98  % (21777)------------------------------
% 28.42/3.98  % (21777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.42/3.98  % (21777)Termination reason: Time limit
% 28.42/3.98  % (21777)Termination phase: Saturation
% 28.42/3.98  
% 28.42/3.98  % (21777)Memory used [KB]: 31726
% 28.42/3.98  % (21777)Time elapsed: 3.0000 s
% 28.42/3.98  % (21777)------------------------------
% 28.42/3.98  % (21777)------------------------------
% 28.42/4.00  % (21772)Time limit reached!
% 28.42/4.00  % (21772)------------------------------
% 28.42/4.00  % (21772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.42/4.00  % (21772)Termination reason: Time limit
% 28.42/4.00  % (21772)Termination phase: Saturation
% 28.42/4.00  
% 28.42/4.00  % (21772)Memory used [KB]: 57312
% 28.42/4.00  % (21772)Time elapsed: 3.400 s
% 28.42/4.00  % (21772)------------------------------
% 28.42/4.00  % (21772)------------------------------
% 30.54/4.19  % (21776)Time limit reached!
% 30.54/4.19  % (21776)------------------------------
% 30.54/4.19  % (21776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.54/4.19  % (21776)Termination reason: Time limit
% 30.54/4.19  % (21776)Termination phase: Saturation
% 30.54/4.19  
% 30.54/4.19  % (21776)Memory used [KB]: 21492
% 30.54/4.19  % (21776)Time elapsed: 3.300 s
% 30.54/4.19  % (21776)------------------------------
% 30.54/4.19  % (21776)------------------------------
% 32.13/4.41  % (21774)Refutation found. Thanks to Tanya!
% 32.13/4.41  % SZS status Theorem for theBenchmark
% 32.13/4.41  % SZS output start Proof for theBenchmark
% 32.13/4.41  fof(f78483,plain,(
% 32.13/4.41    $false),
% 32.13/4.41    inference(subsumption_resolution,[],[f78482,f58])).
% 32.13/4.41  fof(f58,plain,(
% 32.13/4.41    ( ! [X4,X2,X0] : (sP7(X4,X2,X4,X0)) )),
% 32.13/4.41    inference(equality_resolution,[],[f31])).
% 32.13/4.41  fof(f31,plain,(
% 32.13/4.41    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP7(X4,X2,X1,X0)) )),
% 32.13/4.41    inference(cnf_transformation,[],[f12])).
% 32.13/4.41  fof(f12,plain,(
% 32.13/4.41    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 32.13/4.41    inference(ennf_transformation,[],[f3])).
% 32.13/4.41  fof(f3,axiom,(
% 32.13/4.41    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 32.13/4.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 32.13/4.41  fof(f78482,plain,(
% 32.13/4.41    ~sP7(sK0,sK2,sK0,sK0)),
% 32.13/4.41    inference(forward_demodulation,[],[f78481,f77869])).
% 32.13/4.41  fof(f77869,plain,(
% 32.13/4.41    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(subsumption_resolution,[],[f63328,f63312])).
% 32.13/4.41  fof(f63312,plain,(
% 32.13/4.41    sK0 != sK2 | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(equality_factoring,[],[f8915])).
% 32.13/4.41  fof(f8915,plain,(
% 32.13/4.41    sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(duplicate_literal_removal,[],[f8907])).
% 32.13/4.41  fof(f8907,plain,(
% 32.13/4.41    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(resolution,[],[f1870,f33])).
% 32.13/4.41  fof(f33,plain,(
% 32.13/4.41    ( ! [X4,X2,X0,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~sP7(X4,X2,X1,X0)) )),
% 32.13/4.41    inference(cnf_transformation,[],[f12])).
% 32.13/4.41  fof(f1870,plain,(
% 32.13/4.41    sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(resolution,[],[f574,f52])).
% 32.13/4.41  fof(f52,plain,(
% 32.13/4.41    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))) )),
% 32.13/4.41    inference(equality_resolution,[],[f44])).
% 32.13/4.41  fof(f44,plain,(
% 32.13/4.41    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 32.13/4.41    inference(definition_unfolding,[],[f27,f40])).
% 32.13/4.41  fof(f40,plain,(
% 32.13/4.41    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 32.13/4.41    inference(definition_unfolding,[],[f25,f39])).
% 32.13/4.41  fof(f39,plain,(
% 32.13/4.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 32.13/4.41    inference(definition_unfolding,[],[f24,f38])).
% 32.13/4.41  fof(f38,plain,(
% 32.13/4.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 32.13/4.41    inference(cnf_transformation,[],[f7])).
% 32.13/4.41  fof(f7,axiom,(
% 32.13/4.41    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 32.13/4.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 32.13/4.41  fof(f24,plain,(
% 32.13/4.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 32.13/4.41    inference(cnf_transformation,[],[f6])).
% 32.13/4.41  fof(f6,axiom,(
% 32.13/4.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 32.13/4.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 32.13/4.41  fof(f25,plain,(
% 32.13/4.41    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 32.13/4.41    inference(cnf_transformation,[],[f5])).
% 32.13/4.41  fof(f5,axiom,(
% 32.13/4.41    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 32.13/4.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 32.13/4.41  fof(f27,plain,(
% 32.13/4.41    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 32.13/4.41    inference(cnf_transformation,[],[f4])).
% 32.13/4.41  fof(f4,axiom,(
% 32.13/4.41    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 32.13/4.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 32.13/4.41  fof(f574,plain,(
% 32.13/4.41    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0)),
% 32.13/4.41    inference(resolution,[],[f254,f55])).
% 32.13/4.41  fof(f55,plain,(
% 32.13/4.41    ( ! [X4,X2,X0,X1] : (sP7(X4,X2,X1,X0) | ~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))) )),
% 32.13/4.41    inference(equality_resolution,[],[f48])).
% 32.13/4.41  fof(f48,plain,(
% 32.13/4.41    ( ! [X4,X2,X0,X3,X1] : (sP7(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 32.13/4.41    inference(definition_unfolding,[],[f35,f38])).
% 32.13/4.41  fof(f35,plain,(
% 32.13/4.41    ( ! [X4,X2,X0,X3,X1] : (sP7(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 32.13/4.41    inference(cnf_transformation,[],[f12])).
% 32.13/4.41  fof(f254,plain,(
% 32.13/4.41    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(resolution,[],[f125,f17])).
% 32.13/4.41  fof(f17,plain,(
% 32.13/4.41    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~sP4(X3,X1,X0)) )),
% 32.13/4.41    inference(cnf_transformation,[],[f2])).
% 32.13/4.41  fof(f2,axiom,(
% 32.13/4.41    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 32.13/4.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 32.13/4.41  fof(f125,plain,(
% 32.13/4.41    sP4(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(equality_resolution,[],[f68])).
% 32.13/4.41  fof(f68,plain,(
% 32.13/4.41    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | sP4(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0)) )),
% 32.13/4.41    inference(superposition,[],[f41,f21])).
% 32.13/4.41  fof(f21,plain,(
% 32.13/4.41    ( ! [X2,X0,X1] : (sP4(sK3(X0,X1,X2),X1,X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 32.13/4.41    inference(cnf_transformation,[],[f2])).
% 32.13/4.41  fof(f41,plain,(
% 32.13/4.41    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1)),
% 32.13/4.41    inference(definition_unfolding,[],[f15,f40,f39])).
% 32.13/4.41  fof(f15,plain,(
% 32.13/4.41    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 32.13/4.41    inference(cnf_transformation,[],[f11])).
% 32.13/4.41  fof(f11,plain,(
% 32.13/4.41    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 32.13/4.41    inference(flattening,[],[f10])).
% 32.13/4.41  fof(f10,plain,(
% 32.13/4.41    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 32.13/4.41    inference(ennf_transformation,[],[f9])).
% 32.13/4.41  fof(f9,negated_conjecture,(
% 32.13/4.41    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 32.13/4.41    inference(negated_conjecture,[],[f8])).
% 32.13/4.41  fof(f8,conjecture,(
% 32.13/4.41    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 32.13/4.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 32.13/4.41  fof(f63328,plain,(
% 32.13/4.41    sK0 = sK2 | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(subsumption_resolution,[],[f62832,f13])).
% 32.13/4.41  fof(f13,plain,(
% 32.13/4.41    ~r2_hidden(sK2,sK1) | sK0 = sK2),
% 32.13/4.41    inference(cnf_transformation,[],[f11])).
% 32.13/4.41  fof(f62832,plain,(
% 32.13/4.41    r2_hidden(sK2,sK1) | sK0 = sK2 | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(superposition,[],[f505,f8915])).
% 32.13/4.41  fof(f505,plain,(
% 32.13/4.41    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(resolution,[],[f255,f52])).
% 32.13/4.41  fof(f255,plain,(
% 32.13/4.41    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 32.13/4.41    inference(resolution,[],[f125,f18])).
% 32.13/4.41  fof(f18,plain,(
% 32.13/4.41    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~sP4(X3,X1,X0)) )),
% 32.13/4.41    inference(cnf_transformation,[],[f2])).
% 32.13/4.41  fof(f78481,plain,(
% 32.13/4.41    ~sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0)),
% 32.13/4.41    inference(subsumption_resolution,[],[f78480,f14])).
% 32.13/4.41  fof(f14,plain,(
% 32.13/4.41    r2_hidden(sK0,sK1)),
% 32.13/4.41    inference(cnf_transformation,[],[f11])).
% 32.13/4.41  fof(f78480,plain,(
% 32.13/4.41    ~r2_hidden(sK0,sK1) | ~sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0)),
% 32.13/4.41    inference(forward_demodulation,[],[f78479,f77869])).
% 32.13/4.41  fof(f78479,plain,(
% 32.13/4.41    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0)),
% 32.13/4.41    inference(subsumption_resolution,[],[f77929,f54])).
% 32.13/4.41  fof(f54,plain,(
% 32.13/4.41    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 32.13/4.41    inference(equality_resolution,[],[f53])).
% 32.13/4.41  fof(f53,plain,(
% 32.13/4.41    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 32.13/4.41    inference(equality_resolution,[],[f45])).
% 32.13/4.41  fof(f45,plain,(
% 32.13/4.41    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 32.13/4.41    inference(definition_unfolding,[],[f26,f40])).
% 32.13/4.41  fof(f26,plain,(
% 32.13/4.41    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 32.13/4.41    inference(cnf_transformation,[],[f4])).
% 32.13/4.41  fof(f77929,plain,(
% 32.13/4.41    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0)),
% 32.13/4.41    inference(backward_demodulation,[],[f973,f77869])).
% 32.13/4.41  fof(f973,plain,(
% 32.13/4.41    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~sP7(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK2,sK0,sK0)),
% 32.13/4.41    inference(resolution,[],[f277,f56])).
% 32.13/4.41  fof(f56,plain,(
% 32.13/4.41    ( ! [X4,X2,X0,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))) )),
% 32.13/4.41    inference(equality_resolution,[],[f49])).
% 32.13/4.41  fof(f49,plain,(
% 32.13/4.41    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 32.13/4.41    inference(definition_unfolding,[],[f34,f38])).
% 32.13/4.41  fof(f34,plain,(
% 32.13/4.41    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 32.13/4.41    inference(cnf_transformation,[],[f12])).
% 32.13/4.41  fof(f277,plain,(
% 32.13/4.41    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 32.13/4.41    inference(resolution,[],[f130,f16])).
% 32.13/4.41  fof(f16,plain,(
% 32.13/4.41    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | sP4(X3,X1,X0)) )),
% 32.13/4.41    inference(cnf_transformation,[],[f2])).
% 32.13/4.41  fof(f130,plain,(
% 32.13/4.41    ~sP4(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 32.13/4.41    inference(equality_resolution,[],[f69])).
% 32.13/4.41  fof(f69,plain,(
% 32.13/4.41    ( ! [X1] : (k2_enumset1(sK0,sK0,sK0,sK0) != X1 | ~sP4(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X1),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X1),X1)) )),
% 32.13/4.41    inference(superposition,[],[f41,f22])).
% 32.13/4.41  fof(f22,plain,(
% 32.13/4.41    ( ! [X2,X0,X1] : (~sP4(sK3(X0,X1,X2),X1,X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 32.13/4.41    inference(cnf_transformation,[],[f2])).
% 32.13/4.41  % SZS output end Proof for theBenchmark
% 32.13/4.41  % (21774)------------------------------
% 32.13/4.41  % (21774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 32.13/4.41  % (21774)Termination reason: Refutation
% 32.13/4.41  
% 32.13/4.41  % (21774)Memory used [KB]: 19445
% 32.13/4.41  % (21774)Time elapsed: 3.575 s
% 32.13/4.41  % (21774)------------------------------
% 32.13/4.41  % (21774)------------------------------
% 32.13/4.41  % (21738)Success in time 4.044 s
%------------------------------------------------------------------------------
