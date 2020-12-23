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
% DateTime   : Thu Dec  3 12:38:26 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 229 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  106 ( 273 expanded)
%              Number of equality atoms :   47 ( 199 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f587,plain,(
    $false ),
    inference(subsumption_resolution,[],[f576,f141])).

fof(f141,plain,(
    ! [X0] : ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1) ),
    inference(resolution,[],[f60,f27])).

fof(f27,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

% (15622)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (15635)Termination reason: Refutation not found, incomplete strategy

% (15635)Memory used [KB]: 10618
% (15635)Time elapsed: 0.212 s
% (15635)------------------------------
% (15635)------------------------------
% (15623)Refutation not found, incomplete strategy% (15623)------------------------------
% (15623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15623)Termination reason: Refutation not found, incomplete strategy

% (15623)Memory used [KB]: 10618
% (15623)Time elapsed: 0.221 s
% (15623)------------------------------
% (15623)------------------------------
% (15638)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (15622)Refutation not found, incomplete strategy% (15622)------------------------------
% (15622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15622)Termination reason: Refutation not found, incomplete strategy

% (15622)Memory used [KB]: 6140
% (15622)Time elapsed: 0.230 s
% (15622)------------------------------
% (15622)------------------------------
fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f576,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(superposition,[],[f403,f388])).

fof(f388,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(subsumption_resolution,[],[f386,f56])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f386,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f142,f359])).

% (15638)Refutation not found, incomplete strategy% (15638)------------------------------
% (15638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15638)Termination reason: Refutation not found, incomplete strategy

% (15638)Memory used [KB]: 6140
% (15638)Time elapsed: 0.229 s
% (15638)------------------------------
% (15638)------------------------------
fof(f359,plain,(
    ! [X0,X1] : k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(superposition,[],[f57,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f53,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f142,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ r1_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) ),
    inference(forward_demodulation,[],[f74,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f74,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(backward_demodulation,[],[f63,f68])).

fof(f68,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f40,f31])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f63,plain,(
    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) ),
    inference(backward_demodulation,[],[f55,f57])).

fof(f55,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f26,f53,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f52])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f403,plain,(
    ! [X6,X7] : r1_tarski(X6,k5_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X7,X6)))) ),
    inference(superposition,[],[f370,f81])).

fof(f81,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5)) ),
    inference(superposition,[],[f65,f40])).

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f40,f31])).

fof(f370,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f56,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.58  % (15633)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % (15618)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.58  % (15625)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (15626)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.59  % (15617)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.59  % (15634)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.60  % (15625)Refutation not found, incomplete strategy% (15625)------------------------------
% 0.22/0.60  % (15625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (15625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (15625)Memory used [KB]: 1663
% 0.22/0.60  % (15625)Time elapsed: 0.151 s
% 0.22/0.60  % (15625)------------------------------
% 0.22/0.60  % (15625)------------------------------
% 1.89/0.63  % (15628)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.89/0.63  % (15615)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.89/0.63  % (15611)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.89/0.64  % (15624)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.89/0.64  % (15613)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.89/0.64  % (15631)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.89/0.64  % (15627)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.89/0.64  % (15616)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.89/0.64  % (15627)Refutation not found, incomplete strategy% (15627)------------------------------
% 1.89/0.64  % (15627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.64  % (15627)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.64  
% 1.89/0.64  % (15627)Memory used [KB]: 10618
% 1.89/0.64  % (15627)Time elapsed: 0.201 s
% 1.89/0.64  % (15627)------------------------------
% 1.89/0.64  % (15627)------------------------------
% 1.89/0.64  % (15620)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.89/0.65  % (15619)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.89/0.65  % (15623)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.89/0.65  % (15637)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.89/0.65  % (15636)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.89/0.65  % (15637)Refutation not found, incomplete strategy% (15637)------------------------------
% 1.89/0.65  % (15637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.65  % (15637)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.65  
% 1.89/0.65  % (15637)Memory used [KB]: 6140
% 1.89/0.65  % (15637)Time elapsed: 0.211 s
% 1.89/0.65  % (15637)------------------------------
% 1.89/0.65  % (15637)------------------------------
% 1.89/0.65  % (15640)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.89/0.65  % (15640)Refutation not found, incomplete strategy% (15640)------------------------------
% 1.89/0.65  % (15640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.65  % (15636)Refutation not found, incomplete strategy% (15636)------------------------------
% 1.89/0.65  % (15636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.65  % (15628)Refutation not found, incomplete strategy% (15628)------------------------------
% 1.89/0.65  % (15628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.65  % (15636)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.65  
% 1.89/0.65  % (15636)Memory used [KB]: 6140
% 1.89/0.65  % (15636)Time elapsed: 0.161 s
% 1.89/0.65  % (15636)------------------------------
% 1.89/0.65  % (15636)------------------------------
% 1.89/0.65  % (15639)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.89/0.65  % (15635)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.89/0.65  % (15632)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.89/0.65  % (15612)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.89/0.65  % (15628)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.65  
% 1.89/0.65  % (15628)Memory used [KB]: 1663
% 1.89/0.65  % (15628)Time elapsed: 0.159 s
% 1.89/0.65  % (15628)------------------------------
% 1.89/0.65  % (15628)------------------------------
% 1.89/0.65  % (15639)Refutation not found, incomplete strategy% (15639)------------------------------
% 1.89/0.65  % (15639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (15635)Refutation not found, incomplete strategy% (15635)------------------------------
% 2.19/0.66  % (15635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (15614)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 2.19/0.66  % (15612)Refutation not found, incomplete strategy% (15612)------------------------------
% 2.19/0.66  % (15612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (15612)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (15612)Memory used [KB]: 1663
% 2.19/0.66  % (15612)Time elapsed: 0.166 s
% 2.19/0.66  % (15612)------------------------------
% 2.19/0.66  % (15612)------------------------------
% 2.19/0.66  % (15629)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.19/0.66  % (15629)Refutation not found, incomplete strategy% (15629)------------------------------
% 2.19/0.66  % (15629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (15629)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (15629)Memory used [KB]: 1663
% 2.19/0.66  % (15629)Time elapsed: 0.209 s
% 2.19/0.66  % (15629)------------------------------
% 2.19/0.66  % (15629)------------------------------
% 2.19/0.66  % (15621)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.19/0.66  % (15630)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.19/0.66  % (15621)Refutation not found, incomplete strategy% (15621)------------------------------
% 2.19/0.66  % (15621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (15621)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (15621)Memory used [KB]: 10746
% 2.19/0.66  % (15621)Time elapsed: 0.220 s
% 2.19/0.66  % (15621)------------------------------
% 2.19/0.66  % (15621)------------------------------
% 2.19/0.66  % (15640)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (15640)Memory used [KB]: 1663
% 2.19/0.66  % (15640)Time elapsed: 0.213 s
% 2.19/0.66  % (15640)------------------------------
% 2.19/0.66  % (15640)------------------------------
% 2.19/0.66  % (15639)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (15639)Memory used [KB]: 10746
% 2.19/0.66  % (15639)Time elapsed: 0.213 s
% 2.19/0.66  % (15639)------------------------------
% 2.19/0.66  % (15639)------------------------------
% 2.19/0.66  % (15633)Refutation found. Thanks to Tanya!
% 2.19/0.66  % SZS status Theorem for theBenchmark
% 2.19/0.66  % SZS output start Proof for theBenchmark
% 2.19/0.66  fof(f587,plain,(
% 2.19/0.66    $false),
% 2.19/0.66    inference(subsumption_resolution,[],[f576,f141])).
% 2.19/0.66  fof(f141,plain,(
% 2.19/0.66    ( ! [X0] : (~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1)) )),
% 2.19/0.66    inference(resolution,[],[f60,f27])).
% 2.19/0.66  fof(f27,plain,(
% 2.19/0.66    ~r2_hidden(sK0,sK1)),
% 2.19/0.66    inference(cnf_transformation,[],[f21])).
% 2.19/0.66  fof(f21,plain,(
% 2.19/0.66    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.19/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 2.19/0.66  % (15622)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.19/0.67  % (15635)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (15635)Memory used [KB]: 10618
% 2.19/0.67  % (15635)Time elapsed: 0.212 s
% 2.19/0.67  % (15635)------------------------------
% 2.19/0.67  % (15635)------------------------------
% 2.19/0.67  % (15623)Refutation not found, incomplete strategy% (15623)------------------------------
% 2.19/0.67  % (15623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (15623)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (15623)Memory used [KB]: 10618
% 2.19/0.67  % (15623)Time elapsed: 0.221 s
% 2.19/0.67  % (15623)------------------------------
% 2.19/0.67  % (15623)------------------------------
% 2.19/0.67  % (15638)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.19/0.67  % (15622)Refutation not found, incomplete strategy% (15622)------------------------------
% 2.19/0.67  % (15622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (15622)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (15622)Memory used [KB]: 6140
% 2.19/0.67  % (15622)Time elapsed: 0.230 s
% 2.19/0.67  % (15622)------------------------------
% 2.19/0.67  % (15622)------------------------------
% 2.19/0.67  fof(f20,plain,(
% 2.19/0.67    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 2.19/0.67    introduced(choice_axiom,[])).
% 2.19/0.67  fof(f19,plain,(
% 2.19/0.67    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 2.19/0.67    inference(ennf_transformation,[],[f18])).
% 2.19/0.67  fof(f18,negated_conjecture,(
% 2.19/0.67    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.19/0.67    inference(negated_conjecture,[],[f17])).
% 2.19/0.67  fof(f17,conjecture,(
% 2.19/0.67    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 2.19/0.67  fof(f60,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f41,f52])).
% 2.19/0.67  fof(f52,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f33,f51])).
% 2.19/0.67  fof(f51,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f39,f50])).
% 2.19/0.67  fof(f50,plain,(
% 2.19/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f44,f49])).
% 2.19/0.67  fof(f49,plain,(
% 2.19/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f45,f48])).
% 2.19/0.67  fof(f48,plain,(
% 2.19/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f46,f47])).
% 2.19/0.67  fof(f47,plain,(
% 2.19/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f14])).
% 2.19/0.67  fof(f14,axiom,(
% 2.19/0.67    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.19/0.67  fof(f46,plain,(
% 2.19/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f13])).
% 2.19/0.67  fof(f13,axiom,(
% 2.19/0.67    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.19/0.67  fof(f45,plain,(
% 2.19/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f12])).
% 2.19/0.67  fof(f12,axiom,(
% 2.19/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.19/0.67  fof(f44,plain,(
% 2.19/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f11])).
% 2.19/0.67  fof(f11,axiom,(
% 2.19/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.19/0.67  fof(f39,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f10])).
% 2.19/0.67  fof(f10,axiom,(
% 2.19/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.19/0.67  fof(f33,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f9])).
% 2.19/0.68  fof(f9,axiom,(
% 2.19/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.19/0.68  fof(f41,plain,(
% 2.19/0.68    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f25])).
% 2.19/0.68  fof(f25,plain,(
% 2.19/0.68    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.19/0.68    inference(flattening,[],[f24])).
% 2.19/0.68  fof(f24,plain,(
% 2.19/0.68    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.19/0.68    inference(nnf_transformation,[],[f16])).
% 2.19/0.68  fof(f16,axiom,(
% 2.19/0.68    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.19/0.68  fof(f576,plain,(
% 2.19/0.68    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.19/0.68    inference(superposition,[],[f403,f388])).
% 2.19/0.68  fof(f388,plain,(
% 2.19/0.68    sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.19/0.68    inference(subsumption_resolution,[],[f386,f56])).
% 2.19/0.68  fof(f56,plain,(
% 2.19/0.68    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.19/0.68    inference(definition_unfolding,[],[f29,f53])).
% 2.19/0.68  fof(f53,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.19/0.68    inference(definition_unfolding,[],[f32,f52])).
% 2.19/0.68  fof(f32,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f15])).
% 2.19/0.68  fof(f15,axiom,(
% 2.19/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.19/0.68  fof(f29,plain,(
% 2.19/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f5])).
% 2.19/0.68  fof(f5,axiom,(
% 2.19/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.19/0.68  fof(f386,plain,(
% 2.19/0.68    ~r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.19/0.68    inference(backward_demodulation,[],[f142,f359])).
% 2.19/0.68  % (15638)Refutation not found, incomplete strategy% (15638)------------------------------
% 2.19/0.68  % (15638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.68  % (15638)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.68  
% 2.19/0.68  % (15638)Memory used [KB]: 6140
% 2.19/0.68  % (15638)Time elapsed: 0.229 s
% 2.19/0.68  % (15638)------------------------------
% 2.19/0.68  % (15638)------------------------------
% 2.19/0.68  fof(f359,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 2.19/0.68    inference(superposition,[],[f57,f30])).
% 2.19/0.68  fof(f30,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f1])).
% 2.19/0.68  fof(f1,axiom,(
% 2.19/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.19/0.68  fof(f57,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.19/0.68    inference(definition_unfolding,[],[f35,f53,f34])).
% 2.19/0.68  fof(f34,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f4])).
% 2.19/0.68  fof(f4,axiom,(
% 2.19/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.19/0.68  fof(f35,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f7])).
% 2.19/0.68  fof(f7,axiom,(
% 2.19/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.19/0.68  fof(f142,plain,(
% 2.19/0.68    sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~r1_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 2.19/0.68    inference(resolution,[],[f75,f38])).
% 2.19/0.68  fof(f38,plain,(
% 2.19/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f23])).
% 2.19/0.68  fof(f23,plain,(
% 2.19/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.68    inference(flattening,[],[f22])).
% 2.19/0.68  fof(f22,plain,(
% 2.19/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.68    inference(nnf_transformation,[],[f3])).
% 2.19/0.68  fof(f3,axiom,(
% 2.19/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.19/0.68  fof(f75,plain,(
% 2.19/0.68    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)),
% 2.19/0.68    inference(forward_demodulation,[],[f74,f31])).
% 2.19/0.68  fof(f31,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f2])).
% 2.19/0.68  fof(f2,axiom,(
% 2.19/0.68    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.19/0.68  fof(f74,plain,(
% 2.19/0.68    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.19/0.68    inference(backward_demodulation,[],[f63,f68])).
% 2.19/0.68  fof(f68,plain,(
% 2.19/0.68    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 2.19/0.68    inference(superposition,[],[f40,f31])).
% 2.19/0.68  fof(f40,plain,(
% 2.19/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f6])).
% 2.19/0.68  fof(f6,axiom,(
% 2.19/0.68    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.19/0.68  fof(f63,plain,(
% 2.19/0.68    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)),
% 2.19/0.68    inference(backward_demodulation,[],[f55,f57])).
% 2.19/0.68  fof(f55,plain,(
% 2.19/0.68    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 2.19/0.68    inference(definition_unfolding,[],[f26,f53,f54])).
% 2.19/0.68  fof(f54,plain,(
% 2.19/0.68    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.19/0.68    inference(definition_unfolding,[],[f28,f52])).
% 2.19/0.68  fof(f28,plain,(
% 2.19/0.68    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f8])).
% 2.19/0.68  fof(f8,axiom,(
% 2.19/0.68    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.19/0.68  fof(f26,plain,(
% 2.19/0.68    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.19/0.68    inference(cnf_transformation,[],[f21])).
% 2.19/0.68  fof(f403,plain,(
% 2.19/0.68    ( ! [X6,X7] : (r1_tarski(X6,k5_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X7,X6))))) )),
% 2.19/0.68    inference(superposition,[],[f370,f81])).
% 2.19/0.68  fof(f81,plain,(
% 2.19/0.68    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) )),
% 2.19/0.68    inference(superposition,[],[f65,f40])).
% 2.19/0.68  fof(f65,plain,(
% 2.19/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) )),
% 2.19/0.68    inference(superposition,[],[f40,f31])).
% 2.19/0.68  fof(f370,plain,(
% 2.19/0.68    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.19/0.68    inference(superposition,[],[f56,f57])).
% 2.19/0.68  % SZS output end Proof for theBenchmark
% 2.19/0.68  % (15633)------------------------------
% 2.19/0.68  % (15633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.68  % (15633)Termination reason: Refutation
% 2.19/0.68  
% 2.19/0.68  % (15633)Memory used [KB]: 6908
% 2.19/0.68  % (15633)Time elapsed: 0.210 s
% 2.19/0.68  % (15633)------------------------------
% 2.19/0.68  % (15633)------------------------------
% 2.19/0.68  % (15610)Success in time 0.299 s
%------------------------------------------------------------------------------
