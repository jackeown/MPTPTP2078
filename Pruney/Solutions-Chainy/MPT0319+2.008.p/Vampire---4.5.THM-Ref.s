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
% DateTime   : Thu Dec  3 12:42:26 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 174 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 248 expanded)
%              Number of equality atoms :   22 ( 139 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f106,f15,f106,f91])).

fof(f91,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k3_enumset1(X4,X4,X4,X4,X4))
      | X2 = X4
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f81,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f81,plain,(
    ! [X6,X7,X5] :
      ( sP5(X5,k3_enumset1(X6,X6,X6,X6,X6),X7)
      | ~ r2_hidden(X5,X7)
      | X5 = X6 ) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f17,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f19,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( X0 != X1
       => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( X0 != X1
     => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).

fof(f106,plain,(
    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f103,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f35])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f103,plain,(
    ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f96,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f96,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3))
    | ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK3,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ r1_xboole_0(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3)) ),
    inference(definition_unfolding,[],[f14,f35,f35,f35,f35])).

fof(f14,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))
    | ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:28:23 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.48  % (6965)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.17/0.49  % (6957)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.17/0.49  % (6965)Refutation found. Thanks to Tanya!
% 0.17/0.49  % SZS status Theorem for theBenchmark
% 0.17/0.49  % (6954)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.17/0.49  % (6942)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.17/0.49  % SZS output start Proof for theBenchmark
% 0.17/0.50  fof(f110,plain,(
% 0.17/0.50    $false),
% 0.17/0.50    inference(unit_resulting_resolution,[],[f106,f15,f106,f91])).
% 0.17/0.50  fof(f91,plain,(
% 0.17/0.50    ( ! [X4,X2,X3] : (~r2_hidden(X2,k3_enumset1(X4,X4,X4,X4,X4)) | X2 = X4 | ~r2_hidden(X2,X3)) )),
% 0.17/0.50    inference(resolution,[],[f81,f22])).
% 0.17/0.50  fof(f22,plain,(
% 0.17/0.50    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f1])).
% 0.17/0.50  fof(f1,axiom,(
% 0.17/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.17/0.50  fof(f81,plain,(
% 0.17/0.50    ( ! [X6,X7,X5] : (sP5(X5,k3_enumset1(X6,X6,X6,X6,X6),X7) | ~r2_hidden(X5,X7) | X5 = X6) )),
% 0.17/0.50    inference(resolution,[],[f38,f41])).
% 0.17/0.50  fof(f41,plain,(
% 0.17/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 0.17/0.50    inference(equality_resolution,[],[f24])).
% 0.17/0.50  fof(f24,plain,(
% 0.17/0.50    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.17/0.50    inference(cnf_transformation,[],[f1])).
% 0.17/0.50  fof(f38,plain,(
% 0.17/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.17/0.50    inference(definition_unfolding,[],[f29,f35])).
% 0.17/0.50  fof(f35,plain,(
% 0.17/0.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.17/0.50    inference(definition_unfolding,[],[f16,f34])).
% 0.17/0.50  fof(f34,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.17/0.50    inference(definition_unfolding,[],[f17,f33])).
% 0.17/0.50  fof(f33,plain,(
% 0.17/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.17/0.50    inference(definition_unfolding,[],[f19,f30])).
% 0.17/0.50  fof(f30,plain,(
% 0.17/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f5])).
% 0.17/0.50  fof(f5,axiom,(
% 0.17/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.17/0.50  fof(f19,plain,(
% 0.17/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f4])).
% 0.17/0.50  fof(f4,axiom,(
% 0.17/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.17/0.50  fof(f17,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f3])).
% 0.17/0.50  fof(f3,axiom,(
% 0.17/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.17/0.50  fof(f16,plain,(
% 0.17/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f2])).
% 0.17/0.50  fof(f2,axiom,(
% 0.17/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.50  fof(f29,plain,(
% 0.17/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.17/0.50    inference(cnf_transformation,[],[f8])).
% 0.17/0.50  fof(f8,axiom,(
% 0.17/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.17/0.50  fof(f15,plain,(
% 0.17/0.50    sK0 != sK1),
% 0.17/0.50    inference(cnf_transformation,[],[f11])).
% 0.17/0.50  fof(f11,plain,(
% 0.17/0.50    ? [X0,X1,X2,X3] : ((~r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) & X0 != X1)),
% 0.17/0.50    inference(ennf_transformation,[],[f10])).
% 0.17/0.50  fof(f10,negated_conjecture,(
% 0.17/0.50    ~! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.17/0.50    inference(negated_conjecture,[],[f9])).
% 0.17/0.50  fof(f9,conjecture,(
% 0.17/0.50    ! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).
% 0.17/0.50  fof(f106,plain,(
% 0.17/0.50    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.17/0.50    inference(unit_resulting_resolution,[],[f103,f37])).
% 0.17/0.50  fof(f37,plain,(
% 0.17/0.50    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.17/0.50    inference(definition_unfolding,[],[f18,f35])).
% 0.17/0.50  fof(f18,plain,(
% 0.17/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f12])).
% 0.17/0.50  fof(f12,plain,(
% 0.17/0.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.17/0.50    inference(ennf_transformation,[],[f6])).
% 0.17/0.50  fof(f6,axiom,(
% 0.17/0.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.17/0.50  fof(f103,plain,(
% 0.17/0.50    ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.17/0.50    inference(duplicate_literal_removal,[],[f102])).
% 0.17/0.50  fof(f102,plain,(
% 0.17/0.50    ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.17/0.50    inference(resolution,[],[f96,f31])).
% 0.17/0.50  fof(f31,plain,(
% 0.17/0.50    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f13])).
% 0.17/0.50  fof(f13,plain,(
% 0.17/0.50    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.17/0.50    inference(ennf_transformation,[],[f7])).
% 0.17/0.50  fof(f7,axiom,(
% 0.17/0.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.17/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.17/0.50  fof(f96,plain,(
% 0.17/0.50    ~r1_xboole_0(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3)) | ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.17/0.50    inference(resolution,[],[f36,f32])).
% 0.17/0.50  fof(f32,plain,(
% 0.17/0.50    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f13])).
% 0.17/0.50  fof(f36,plain,(
% 0.17/0.50    ~r1_xboole_0(k2_zfmisc_1(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK3,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~r1_xboole_0(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3))),
% 0.17/0.50    inference(definition_unfolding,[],[f14,f35,f35,f35,f35])).
% 0.17/0.50  fof(f14,plain,(
% 0.17/0.50    ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) | ~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))),
% 0.17/0.50    inference(cnf_transformation,[],[f11])).
% 0.17/0.50  % SZS output end Proof for theBenchmark
% 0.17/0.50  % (6965)------------------------------
% 0.17/0.50  % (6965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.50  % (6965)Termination reason: Refutation
% 0.17/0.50  
% 0.17/0.50  % (6965)Memory used [KB]: 6268
% 0.17/0.50  % (6965)Time elapsed: 0.115 s
% 0.17/0.50  % (6965)------------------------------
% 0.17/0.50  % (6965)------------------------------
% 0.17/0.50  % (6939)Success in time 0.16 s
%------------------------------------------------------------------------------
