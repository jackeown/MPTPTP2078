%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:47 EST 2020

% Result     : Theorem 1.11s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 238 expanded)
%              Number of leaves         :   13 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 575 expanded)
%              Number of equality atoms :   82 ( 421 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f75,f43,f88,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f38])).

% (23391)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f88,plain,(
    ~ r2_hidden(sK3(sK1,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f75,f24])).

fof(f24,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & sK0 != k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f43,plain,(
    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f22,f42])).

fof(f22,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    sK1 != sK3(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f43,f71,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f52,f68])).

fof(f68,plain,(
    sK1 = sK2(sK0) ),
    inference(unit_resulting_resolution,[],[f52,f24])).

fof(f52,plain,(
    r2_hidden(sK2(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f23,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:16:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.39  ipcrm: permission denied for id (823459845)
% 0.15/0.39  ipcrm: permission denied for id (823525386)
% 0.15/0.41  ipcrm: permission denied for id (823689241)
% 0.15/0.42  ipcrm: permission denied for id (823722011)
% 0.22/0.43  ipcrm: permission denied for id (823820324)
% 0.22/0.44  ipcrm: permission denied for id (823918637)
% 0.22/0.44  ipcrm: permission denied for id (824016946)
% 0.22/0.44  ipcrm: permission denied for id (824049715)
% 0.22/0.45  ipcrm: permission denied for id (824082491)
% 0.22/0.45  ipcrm: permission denied for id (824180805)
% 0.22/0.45  ipcrm: permission denied for id (824213574)
% 0.22/0.46  ipcrm: permission denied for id (824279119)
% 0.22/0.47  ipcrm: permission denied for id (824311889)
% 0.22/0.48  ipcrm: permission denied for id (824410205)
% 0.22/0.48  ipcrm: permission denied for id (824475744)
% 0.22/0.51  ipcrm: permission denied for id (824574069)
% 0.22/0.52  ipcrm: permission denied for id (824672383)
% 0.73/0.65  % (23380)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.11/0.65  % (23380)Refutation found. Thanks to Tanya!
% 1.11/0.65  % SZS status Theorem for theBenchmark
% 1.11/0.65  % (23399)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.11/0.65  % SZS output start Proof for theBenchmark
% 1.11/0.65  fof(f100,plain,(
% 1.11/0.65    $false),
% 1.11/0.65    inference(unit_resulting_resolution,[],[f75,f43,f88,f45])).
% 1.11/0.65  fof(f45,plain,(
% 1.11/0.65    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 1.11/0.65    inference(definition_unfolding,[],[f30,f42])).
% 1.11/0.65  fof(f42,plain,(
% 1.11/0.65    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.11/0.65    inference(definition_unfolding,[],[f25,f41])).
% 1.11/0.65  fof(f41,plain,(
% 1.11/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.11/0.65    inference(definition_unfolding,[],[f27,f40])).
% 1.11/0.65  fof(f40,plain,(
% 1.11/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.11/0.65    inference(definition_unfolding,[],[f32,f39])).
% 1.11/0.65  fof(f39,plain,(
% 1.11/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.11/0.65    inference(definition_unfolding,[],[f33,f38])).
% 1.11/0.65  % (23391)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.11/0.65  fof(f38,plain,(
% 1.11/0.65    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.11/0.65    inference(definition_unfolding,[],[f34,f37])).
% 1.11/0.65  fof(f37,plain,(
% 1.11/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.11/0.65    inference(definition_unfolding,[],[f35,f36])).
% 1.11/0.65  fof(f36,plain,(
% 1.11/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f9])).
% 1.11/0.65  fof(f9,axiom,(
% 1.11/0.65    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.11/0.65  fof(f35,plain,(
% 1.11/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f8])).
% 1.11/0.65  fof(f8,axiom,(
% 1.11/0.65    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.11/0.65  fof(f34,plain,(
% 1.11/0.65    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f7])).
% 1.11/0.65  fof(f7,axiom,(
% 1.11/0.65    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.11/0.65  fof(f33,plain,(
% 1.11/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f6])).
% 1.11/0.65  fof(f6,axiom,(
% 1.11/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.11/0.65  fof(f32,plain,(
% 1.11/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f5])).
% 1.11/0.65  fof(f5,axiom,(
% 1.11/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.11/0.65  fof(f27,plain,(
% 1.11/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f4])).
% 1.11/0.65  fof(f4,axiom,(
% 1.11/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.11/0.65  fof(f25,plain,(
% 1.11/0.65    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f3])).
% 1.11/0.65  fof(f3,axiom,(
% 1.11/0.65    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.11/0.65  fof(f30,plain,(
% 1.11/0.65    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f21])).
% 1.11/0.65  fof(f21,plain,(
% 1.11/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 1.11/0.65  fof(f20,plain,(
% 1.11/0.65    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.11/0.65    introduced(choice_axiom,[])).
% 1.11/0.65  fof(f19,plain,(
% 1.11/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.11/0.65    inference(rectify,[],[f18])).
% 1.11/0.65  fof(f18,plain,(
% 1.11/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.11/0.65    inference(nnf_transformation,[],[f2])).
% 1.11/0.65  fof(f2,axiom,(
% 1.11/0.65    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.11/0.65  fof(f88,plain,(
% 1.11/0.65    ~r2_hidden(sK3(sK1,sK0),sK0)),
% 1.11/0.65    inference(unit_resulting_resolution,[],[f75,f24])).
% 1.11/0.65  fof(f24,plain,(
% 1.11/0.65    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 1.11/0.65    inference(cnf_transformation,[],[f15])).
% 1.11/0.65  fof(f15,plain,(
% 1.11/0.65    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 1.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 1.11/0.65  fof(f14,plain,(
% 1.11/0.65    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 1.11/0.65    introduced(choice_axiom,[])).
% 1.11/0.65  fof(f12,plain,(
% 1.11/0.65    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.11/0.65    inference(ennf_transformation,[],[f11])).
% 1.11/0.65  fof(f11,negated_conjecture,(
% 1.11/0.65    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.11/0.65    inference(negated_conjecture,[],[f10])).
% 1.11/0.65  fof(f10,conjecture,(
% 1.11/0.65    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.11/0.65  fof(f43,plain,(
% 1.11/0.65    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.11/0.65    inference(definition_unfolding,[],[f22,f42])).
% 1.11/0.65  fof(f22,plain,(
% 1.11/0.65    sK0 != k1_tarski(sK1)),
% 1.11/0.65    inference(cnf_transformation,[],[f15])).
% 1.11/0.65  fof(f75,plain,(
% 1.11/0.65    sK1 != sK3(sK1,sK0)),
% 1.11/0.65    inference(unit_resulting_resolution,[],[f43,f71,f51])).
% 1.11/0.65  fof(f51,plain,(
% 1.11/0.65    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(X0,X1)) )),
% 1.11/0.65    inference(inner_rewriting,[],[f44])).
% 1.11/0.65  fof(f44,plain,(
% 1.11/0.65    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.11/0.65    inference(definition_unfolding,[],[f31,f42])).
% 1.11/0.65  fof(f31,plain,(
% 1.11/0.65    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.11/0.65    inference(cnf_transformation,[],[f21])).
% 1.11/0.65  fof(f71,plain,(
% 1.11/0.65    r2_hidden(sK1,sK0)),
% 1.11/0.65    inference(backward_demodulation,[],[f52,f68])).
% 1.11/0.65  fof(f68,plain,(
% 1.11/0.65    sK1 = sK2(sK0)),
% 1.11/0.65    inference(unit_resulting_resolution,[],[f52,f24])).
% 1.11/0.65  fof(f52,plain,(
% 1.11/0.65    r2_hidden(sK2(sK0),sK0)),
% 1.11/0.65    inference(unit_resulting_resolution,[],[f23,f26])).
% 1.11/0.65  fof(f26,plain,(
% 1.11/0.65    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.11/0.65    inference(cnf_transformation,[],[f17])).
% 1.11/0.65  fof(f17,plain,(
% 1.11/0.65    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f16])).
% 1.11/0.65  fof(f16,plain,(
% 1.11/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.11/0.65    introduced(choice_axiom,[])).
% 1.11/0.65  fof(f13,plain,(
% 1.11/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.11/0.65    inference(ennf_transformation,[],[f1])).
% 1.11/0.65  fof(f1,axiom,(
% 1.11/0.65    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.11/0.65  fof(f23,plain,(
% 1.11/0.65    k1_xboole_0 != sK0),
% 1.11/0.65    inference(cnf_transformation,[],[f15])).
% 1.11/0.65  % SZS output end Proof for theBenchmark
% 1.11/0.65  % (23380)------------------------------
% 1.11/0.65  % (23380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.11/0.65  % (23380)Termination reason: Refutation
% 1.11/0.65  
% 1.11/0.65  % (23380)Memory used [KB]: 1791
% 1.11/0.65  % (23380)Time elapsed: 0.084 s
% 1.11/0.65  % (23380)------------------------------
% 1.11/0.65  % (23380)------------------------------
% 1.11/0.66  % (23211)Success in time 0.281 s
%------------------------------------------------------------------------------
