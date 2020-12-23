%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 143 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 289 expanded)
%              Number of equality atoms :   75 ( 158 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f810,plain,(
    $false ),
    inference(global_subsumption,[],[f41,f800,f799])).

fof(f799,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f411,f783])).

fof(f783,plain,(
    ! [X0] : k4_xboole_0(X0,k1_enumset1(X0,X0,X0)) = X0 ),
    inference(trivial_inequality_removal,[],[f782])).

fof(f782,plain,(
    ! [X0] :
      ( X0 != X0
      | k4_xboole_0(X0,k1_enumset1(X0,X0,X0)) = X0 ) ),
    inference(equality_factoring,[],[f145])).

fof(f145,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,k1_enumset1(X5,X5,X5)) = X4
      | k4_xboole_0(X5,k1_enumset1(X4,X4,X4)) = X5 ) ),
    inference(resolution,[],[f133,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0 ) ),
    inference(resolution,[],[f73,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f411,plain,(
    ! [X2,X0] : k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k1_enumset1(X0,X0,X2)) ),
    inference(forward_demodulation,[],[f403,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k1_enumset1(X0,X0,X2) = k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(global_subsumption,[],[f77,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X0,X2) = k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k1_enumset1(X0,X0,X2)
      | k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(definition_unfolding,[],[f70,f50,f50])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k2_tarski(X0,X2)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(definition_unfolding,[],[f69,f50])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f403,plain,(
    ! [X2,X0,X3,X1] : k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) ),
    inference(resolution,[],[f389,f77])).

fof(f389,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f384,f100])).

fof(f100,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f49,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f384,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f148,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k4_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f47,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f800,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f476,f783])).

fof(f476,plain,(
    ! [X10,X11] : k1_xboole_0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_enumset1(X10,X10,X11)) ),
    inference(resolution,[],[f470,f58])).

fof(f470,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k1_xboole_0),k1_enumset1(X0,X0,X1)) ),
    inference(subsumption_resolution,[],[f469,f100])).

fof(f469,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_enumset1(X0,X0,X1))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f272,f42])).

fof(f272,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X4,k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | r1_tarski(k2_relat_1(X4),k1_enumset1(X1,X1,X3))
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f270,f77])).

fof(f270,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(k2_relat_1(X4),k1_enumset1(X1,X1,X3))
      | ~ r1_tarski(X4,k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f48,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k1_enumset1(X1,X1,X3) = k2_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(global_subsumption,[],[f77,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X1,X1,X3) = k2_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X4) = k1_enumset1(X1,X1,X3)
      | k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(definition_unfolding,[],[f71,f50,f50])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X4) = k2_tarski(X1,X3)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (9786)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.47  % (9786)Refutation not found, incomplete strategy% (9786)------------------------------
% 0.21/0.47  % (9786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9780)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (9786)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (9786)Memory used [KB]: 10618
% 0.21/0.47  % (9786)Time elapsed: 0.061 s
% 0.21/0.47  % (9786)------------------------------
% 0.21/0.47  % (9786)------------------------------
% 0.21/0.49  % (9780)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f810,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f41,f800,f799])).
% 0.21/0.49  fof(f799,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(superposition,[],[f411,f783])).
% 0.21/0.49  fof(f783,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f782])).
% 0.21/0.49  fof(f782,plain,(
% 0.21/0.49    ( ! [X0] : (X0 != X0 | k4_xboole_0(X0,k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.49    inference(equality_factoring,[],[f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_xboole_0(X4,k1_enumset1(X5,X5,X5)) = X4 | k4_xboole_0(X5,k1_enumset1(X4,X4,X4)) = X5) )),
% 0.21/0.49    inference(resolution,[],[f133,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f60,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f43,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0) )),
% 0.21/0.49    inference(resolution,[],[f73,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.49  fof(f411,plain,(
% 0.21/0.49    ( ! [X2,X0] : (k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k1_enumset1(X0,X0,X2))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f403,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X0,X2) = k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.49    inference(global_subsumption,[],[f77,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X0,X2) = k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k1_enumset1(X0,X0,X2) | k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f70,f50,f50])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k2_tarski(X0,X2) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f69,f50])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.21/0.49  fof(f403,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))))) )),
% 0.21/0.49    inference(resolution,[],[f389,f77])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f384,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(superposition,[],[f49,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f384,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f148,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_xboole_0 = k4_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.21/0.49    inference(resolution,[],[f47,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.50  fof(f800,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f476,f783])).
% 0.21/0.50  fof(f476,plain,(
% 0.21/0.50    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_enumset1(X10,X10,X11))) )),
% 0.21/0.50    inference(resolution,[],[f470,f58])).
% 0.21/0.50  fof(f470,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k1_xboole_0),k1_enumset1(X0,X0,X1))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f469,f100])).
% 0.21/0.50  fof(f469,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k1_xboole_0),k1_enumset1(X0,X0,X1)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f272,f42])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(X4,k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) | r1_tarski(k2_relat_1(X4),k1_enumset1(X1,X1,X3)) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f270,f77])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k2_relat_1(X4),k1_enumset1(X1,X1,X3)) | ~r1_tarski(X4,k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(superposition,[],[f48,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k1_enumset1(X1,X1,X3) = k2_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.50    inference(global_subsumption,[],[f77,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k1_enumset1(X1,X1,X3) = k2_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X4) = k1_enumset1(X1,X1,X3) | k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f71,f50,f50])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X4) = k2_tarski(X1,X3) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,negated_conjecture,(
% 0.21/0.50    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.50    inference(negated_conjecture,[],[f17])).
% 0.21/0.50  fof(f17,conjecture,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (9780)------------------------------
% 0.21/0.50  % (9780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9780)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (9780)Memory used [KB]: 11257
% 0.21/0.50  % (9780)Time elapsed: 0.078 s
% 0.21/0.50  % (9780)------------------------------
% 0.21/0.50  % (9780)------------------------------
% 0.21/0.50  % (9771)Success in time 0.137 s
%------------------------------------------------------------------------------
