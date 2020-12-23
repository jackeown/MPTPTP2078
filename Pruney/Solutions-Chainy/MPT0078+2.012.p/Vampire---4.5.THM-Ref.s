%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:48 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 139 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 297 expanded)
%              Number of equality atoms :   54 ( 136 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(subsumption_resolution,[],[f297,f34])).

fof(f34,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f297,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f296,f199])).

fof(f199,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f176,f59])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f176,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f52,f171])).

fof(f171,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f88,f97])).

fof(f97,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f53,f32])).

fof(f32,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f296,plain,(
    sK2 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f295,f234])).

fof(f234,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f190,f59])).

fof(f190,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f52,f172])).

fof(f172,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f88,f98])).

fof(f98,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f295,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f281,f146])).

fof(f146,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(forward_demodulation,[],[f129,f38])).

fof(f129,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0) ),
    inference(superposition,[],[f50,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f51,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f281,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f141,f58])).

fof(f58,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f42,f31])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f141,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f124,f59])).

fof(f124,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f50,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (798261248)
% 0.13/0.37  ipcrm: permission denied for id (798294018)
% 0.21/0.37  ipcrm: permission denied for id (798326788)
% 0.21/0.37  ipcrm: permission denied for id (798359558)
% 0.21/0.37  ipcrm: permission denied for id (798392328)
% 0.21/0.38  ipcrm: permission denied for id (798425099)
% 0.21/0.39  ipcrm: permission denied for id (798621717)
% 0.21/0.39  ipcrm: permission denied for id (798654486)
% 0.21/0.39  ipcrm: permission denied for id (798687255)
% 0.21/0.39  ipcrm: permission denied for id (798720024)
% 0.21/0.39  ipcrm: permission denied for id (798752793)
% 0.21/0.40  ipcrm: permission denied for id (798785562)
% 0.21/0.40  ipcrm: permission denied for id (798818332)
% 0.21/0.40  ipcrm: permission denied for id (798851102)
% 0.21/0.41  ipcrm: permission denied for id (798916642)
% 0.21/0.41  ipcrm: permission denied for id (798949411)
% 0.21/0.41  ipcrm: permission denied for id (798982180)
% 0.21/0.41  ipcrm: permission denied for id (799014949)
% 0.21/0.41  ipcrm: permission denied for id (799047718)
% 0.21/0.41  ipcrm: permission denied for id (799080487)
% 0.21/0.41  ipcrm: permission denied for id (799113256)
% 0.21/0.41  ipcrm: permission denied for id (799146025)
% 0.21/0.42  ipcrm: permission denied for id (799178794)
% 0.21/0.42  ipcrm: permission denied for id (799211563)
% 0.21/0.42  ipcrm: permission denied for id (799244332)
% 0.21/0.42  ipcrm: permission denied for id (799277101)
% 0.21/0.42  ipcrm: permission denied for id (799309871)
% 0.21/0.43  ipcrm: permission denied for id (799539256)
% 0.21/0.43  ipcrm: permission denied for id (799572025)
% 0.21/0.45  ipcrm: permission denied for id (799801413)
% 0.21/0.45  ipcrm: permission denied for id (799932489)
% 0.21/0.46  ipcrm: permission denied for id (799965258)
% 0.21/0.46  ipcrm: permission denied for id (799998027)
% 0.21/0.46  ipcrm: permission denied for id (800129103)
% 0.21/0.46  ipcrm: permission denied for id (800161872)
% 0.21/0.46  ipcrm: permission denied for id (800194641)
% 0.21/0.47  ipcrm: permission denied for id (800325720)
% 0.21/0.48  ipcrm: permission denied for id (800358490)
% 0.21/0.48  ipcrm: permission denied for id (800456800)
% 0.21/0.49  ipcrm: permission denied for id (800555107)
% 0.21/0.49  ipcrm: permission denied for id (800587877)
% 0.21/0.50  ipcrm: permission denied for id (800620656)
% 0.21/0.51  ipcrm: permission denied for id (800686196)
% 0.21/0.51  ipcrm: permission denied for id (800817272)
% 0.21/0.51  ipcrm: permission denied for id (800850041)
% 0.21/0.52  ipcrm: permission denied for id (801013887)
% 0.39/0.65  % (17448)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.39/0.66  % (17461)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.39/0.67  % (17456)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.39/0.67  % (17456)Refutation not found, incomplete strategy% (17456)------------------------------
% 0.39/0.67  % (17456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.67  % (17456)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.67  
% 0.39/0.67  % (17456)Memory used [KB]: 10618
% 0.39/0.67  % (17456)Time elapsed: 0.105 s
% 0.39/0.67  % (17456)------------------------------
% 0.39/0.67  % (17456)------------------------------
% 0.39/0.67  % (17447)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.39/0.67  % (17469)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.39/0.67  % (17455)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.39/0.68  % (17444)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.39/0.68  % (17462)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.39/0.69  % (17452)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.39/0.69  % (17464)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.39/0.70  % (17468)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.39/0.70  % (17446)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.39/0.70  % (17449)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.39/0.70  % (17466)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.39/0.71  % (17460)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.39/0.71  % (17460)Refutation not found, incomplete strategy% (17460)------------------------------
% 0.39/0.71  % (17460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.71  % (17460)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.71  
% 0.39/0.71  % (17460)Memory used [KB]: 10618
% 0.39/0.71  % (17460)Time elapsed: 0.133 s
% 0.39/0.71  % (17460)------------------------------
% 0.39/0.71  % (17460)------------------------------
% 0.39/0.71  % (17473)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.39/0.71  % (17454)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.39/0.72  % (17465)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.39/0.72  % (17458)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.39/0.72  % (17463)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.39/0.72  % (17450)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.72  % (17453)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.39/0.72  % (17457)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.39/0.73  % (17466)Refutation found. Thanks to Tanya!
% 0.39/0.73  % SZS status Theorem for theBenchmark
% 0.39/0.73  % SZS output start Proof for theBenchmark
% 0.39/0.73  fof(f298,plain,(
% 0.39/0.73    $false),
% 0.39/0.73    inference(subsumption_resolution,[],[f297,f34])).
% 0.39/0.73  fof(f34,plain,(
% 0.39/0.73    sK0 != sK2),
% 0.39/0.73    inference(cnf_transformation,[],[f24])).
% 0.39/0.73  fof(f24,plain,(
% 0.39/0.73    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.39/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).
% 0.39/0.73  fof(f23,plain,(
% 0.39/0.73    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 0.39/0.73    introduced(choice_axiom,[])).
% 0.39/0.73  fof(f19,plain,(
% 0.39/0.73    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 0.39/0.73    inference(flattening,[],[f18])).
% 0.39/0.73  fof(f18,plain,(
% 0.39/0.73    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 0.39/0.73    inference(ennf_transformation,[],[f16])).
% 0.39/0.73  fof(f16,negated_conjecture,(
% 0.39/0.73    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.39/0.73    inference(negated_conjecture,[],[f15])).
% 0.39/0.73  fof(f15,conjecture,(
% 0.39/0.73    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 0.39/0.73  fof(f297,plain,(
% 0.39/0.73    sK0 = sK2),
% 0.39/0.73    inference(forward_demodulation,[],[f296,f199])).
% 0.39/0.73  fof(f199,plain,(
% 0.39/0.73    sK0 = k4_xboole_0(sK0,sK1)),
% 0.39/0.73    inference(superposition,[],[f176,f59])).
% 0.39/0.73  fof(f59,plain,(
% 0.39/0.73    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.39/0.73    inference(superposition,[],[f42,f38])).
% 0.39/0.73  fof(f38,plain,(
% 0.39/0.73    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.39/0.73    inference(cnf_transformation,[],[f5])).
% 0.39/0.73  fof(f5,axiom,(
% 0.39/0.73    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.39/0.73  fof(f42,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f1])).
% 0.39/0.73  fof(f1,axiom,(
% 0.39/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.39/0.73  fof(f176,plain,(
% 0.39/0.73    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.39/0.73    inference(superposition,[],[f52,f171])).
% 0.39/0.73  fof(f171,plain,(
% 0.39/0.73    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.39/0.73    inference(resolution,[],[f88,f97])).
% 0.39/0.73  fof(f97,plain,(
% 0.39/0.73    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 0.39/0.73    inference(resolution,[],[f53,f32])).
% 0.39/0.73  fof(f32,plain,(
% 0.39/0.73    r1_xboole_0(sK0,sK1)),
% 0.39/0.73    inference(cnf_transformation,[],[f24])).
% 0.39/0.73  fof(f53,plain,(
% 0.39/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.39/0.73    inference(definition_unfolding,[],[f47,f43])).
% 0.39/0.73  fof(f43,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f12])).
% 0.39/0.73  fof(f12,axiom,(
% 0.39/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.39/0.73  fof(f47,plain,(
% 0.39/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f30])).
% 0.39/0.73  fof(f30,plain,(
% 0.39/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.39/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f29])).
% 0.39/0.73  fof(f29,plain,(
% 0.39/0.73    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.39/0.73    introduced(choice_axiom,[])).
% 0.39/0.73  fof(f20,plain,(
% 0.39/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.39/0.73    inference(ennf_transformation,[],[f17])).
% 0.39/0.73  fof(f17,plain,(
% 0.39/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.39/0.73    inference(rectify,[],[f4])).
% 0.39/0.73  fof(f4,axiom,(
% 0.39/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.39/0.73  fof(f88,plain,(
% 0.39/0.73    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.39/0.73    inference(resolution,[],[f68,f40])).
% 0.39/0.73  fof(f40,plain,(
% 0.39/0.73    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f28])).
% 0.39/0.73  fof(f28,plain,(
% 0.39/0.73    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.39/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.39/0.73  fof(f27,plain,(
% 0.39/0.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.39/0.73    introduced(choice_axiom,[])).
% 0.39/0.73  fof(f26,plain,(
% 0.39/0.73    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.39/0.73    inference(rectify,[],[f25])).
% 0.39/0.73  fof(f25,plain,(
% 0.39/0.73    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.39/0.73    inference(nnf_transformation,[],[f2])).
% 0.39/0.73  fof(f2,axiom,(
% 0.39/0.73    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.39/0.73  fof(f68,plain,(
% 0.39/0.73    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.39/0.73    inference(resolution,[],[f49,f35])).
% 0.39/0.73  fof(f35,plain,(
% 0.39/0.73    v1_xboole_0(k1_xboole_0)),
% 0.39/0.73    inference(cnf_transformation,[],[f3])).
% 0.39/0.73  fof(f3,axiom,(
% 0.39/0.73    v1_xboole_0(k1_xboole_0)),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.39/0.73  fof(f49,plain,(
% 0.39/0.73    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f22])).
% 0.39/0.73  fof(f22,plain,(
% 0.39/0.73    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.39/0.73    inference(ennf_transformation,[],[f14])).
% 0.39/0.73  fof(f14,axiom,(
% 0.39/0.73    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.39/0.73  fof(f52,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.39/0.73    inference(definition_unfolding,[],[f45,f43])).
% 0.39/0.73  fof(f45,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.39/0.73    inference(cnf_transformation,[],[f13])).
% 0.39/0.73  fof(f13,axiom,(
% 0.39/0.73    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.39/0.73  fof(f296,plain,(
% 0.39/0.73    sK2 = k4_xboole_0(sK0,sK1)),
% 0.39/0.73    inference(forward_demodulation,[],[f295,f234])).
% 0.39/0.73  fof(f234,plain,(
% 0.39/0.73    sK2 = k4_xboole_0(sK2,sK1)),
% 0.39/0.73    inference(superposition,[],[f190,f59])).
% 0.39/0.73  fof(f190,plain,(
% 0.39/0.73    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 0.39/0.73    inference(superposition,[],[f52,f172])).
% 0.39/0.73  fof(f172,plain,(
% 0.39/0.73    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 0.39/0.73    inference(resolution,[],[f88,f98])).
% 0.39/0.73  fof(f98,plain,(
% 0.39/0.73    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) )),
% 0.39/0.73    inference(resolution,[],[f53,f33])).
% 0.39/0.73  fof(f33,plain,(
% 0.39/0.73    r1_xboole_0(sK2,sK1)),
% 0.39/0.73    inference(cnf_transformation,[],[f24])).
% 0.39/0.73  fof(f295,plain,(
% 0.39/0.73    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1)),
% 0.39/0.73    inference(forward_demodulation,[],[f281,f146])).
% 0.39/0.73  fof(f146,plain,(
% 0.39/0.73    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X3,X2),X2)) )),
% 0.39/0.73    inference(forward_demodulation,[],[f129,f38])).
% 0.39/0.73  fof(f129,plain,(
% 0.39/0.73    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0)) )),
% 0.39/0.73    inference(superposition,[],[f50,f55])).
% 0.39/0.73  fof(f55,plain,(
% 0.39/0.73    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.39/0.73    inference(backward_demodulation,[],[f51,f37])).
% 0.39/0.73  fof(f37,plain,(
% 0.39/0.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.39/0.73    inference(cnf_transformation,[],[f9])).
% 0.39/0.73  fof(f9,axiom,(
% 0.39/0.73    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.39/0.73  fof(f51,plain,(
% 0.39/0.73    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.39/0.73    inference(definition_unfolding,[],[f36,f43])).
% 0.39/0.73  fof(f36,plain,(
% 0.39/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f6])).
% 0.39/0.73  fof(f6,axiom,(
% 0.39/0.73    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.39/0.73  fof(f50,plain,(
% 0.39/0.73    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f10])).
% 0.39/0.73  fof(f10,axiom,(
% 0.39/0.73    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.39/0.73  fof(f281,plain,(
% 0.39/0.73    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.39/0.73    inference(superposition,[],[f141,f58])).
% 0.39/0.73  fof(f58,plain,(
% 0.39/0.73    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)),
% 0.39/0.73    inference(superposition,[],[f42,f31])).
% 0.39/0.73  fof(f31,plain,(
% 0.39/0.73    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.39/0.73    inference(cnf_transformation,[],[f24])).
% 0.39/0.73  fof(f141,plain,(
% 0.39/0.73    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X2,X3),X2)) )),
% 0.39/0.73    inference(forward_demodulation,[],[f124,f59])).
% 0.39/0.73  fof(f124,plain,(
% 0.39/0.73    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2))) )),
% 0.39/0.73    inference(superposition,[],[f50,f55])).
% 0.39/0.73  % SZS output end Proof for theBenchmark
% 0.39/0.73  % (17466)------------------------------
% 0.39/0.73  % (17466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.73  % (17466)Termination reason: Refutation
% 0.39/0.73  
% 0.39/0.73  % (17466)Memory used [KB]: 6396
% 0.39/0.73  % (17466)Time elapsed: 0.092 s
% 0.39/0.73  % (17466)------------------------------
% 0.39/0.73  % (17466)------------------------------
% 0.39/0.73  % (17445)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.39/0.73  % (17285)Success in time 0.372 s
%------------------------------------------------------------------------------
