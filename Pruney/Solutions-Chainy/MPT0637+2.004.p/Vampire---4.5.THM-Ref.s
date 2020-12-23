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
% DateTime   : Thu Dec  3 12:52:22 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 140 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 229 expanded)
%              Number of equality atoms :   38 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f378,plain,(
    $false ),
    inference(resolution,[],[f319,f190])).

fof(f190,plain,(
    ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f109,f80])).

fof(f80,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(forward_demodulation,[],[f69,f62])).

fof(f62,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unit_resulting_resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f69,plain,
    ( ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1))
    | ~ r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f54,f62])).

fof(f54,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) ),
    inference(extensionality_resolution,[],[f30,f27])).

fof(f27,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f109,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f108,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f108,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) ),
    inference(subsumption_resolution,[],[f107,f40])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f71,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f46,f62])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f319,plain,(
    ! [X4,X5] : r1_tarski(k6_relat_1(k3_xboole_0(X4,X5)),k7_relat_1(k6_relat_1(X4),X5)) ),
    inference(superposition,[],[f167,f196])).

fof(f196,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f62,f103])).

fof(f103,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f99,f41])).

fof(f99,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f43,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f167,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f72,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f160,f62])).

fof(f160,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f159,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X0,X2)) ),
    inference(backward_demodulation,[],[f77,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2)) ),
    inference(unit_resulting_resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f77,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f63,f62])).

fof(f63,plain,(
    ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f40,f40,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f159,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f126,f62])).

fof(f126,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(unit_resulting_resolution,[],[f40,f40,f40,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f72,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f47,f62])).

fof(f47,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f45,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (5898)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.47  % (5898)Refutation not found, incomplete strategy% (5898)------------------------------
% 0.22/0.47  % (5898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (5898)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (5898)Memory used [KB]: 10618
% 0.22/0.47  % (5898)Time elapsed: 0.052 s
% 0.22/0.47  % (5898)------------------------------
% 0.22/0.47  % (5898)------------------------------
% 0.22/0.48  % (5912)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.48  % (5912)Refutation not found, incomplete strategy% (5912)------------------------------
% 0.22/0.48  % (5912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5912)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (5912)Memory used [KB]: 6140
% 0.22/0.48  % (5912)Time elapsed: 0.065 s
% 0.22/0.48  % (5912)------------------------------
% 0.22/0.48  % (5912)------------------------------
% 0.22/0.51  % (5892)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (5889)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (5908)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (5900)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (5900)Refutation not found, incomplete strategy% (5900)------------------------------
% 0.22/0.52  % (5900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5900)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (5900)Memory used [KB]: 1663
% 0.22/0.52  % (5900)Time elapsed: 0.083 s
% 0.22/0.52  % (5900)------------------------------
% 0.22/0.52  % (5900)------------------------------
% 0.22/0.53  % (5887)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (5887)Refutation not found, incomplete strategy% (5887)------------------------------
% 0.22/0.53  % (5887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5887)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5887)Memory used [KB]: 1663
% 0.22/0.53  % (5887)Time elapsed: 0.124 s
% 0.22/0.53  % (5887)------------------------------
% 0.22/0.53  % (5887)------------------------------
% 0.22/0.53  % (5896)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (5890)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (5915)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (5915)Refutation not found, incomplete strategy% (5915)------------------------------
% 0.22/0.54  % (5915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5915)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5915)Memory used [KB]: 1663
% 0.22/0.54  % (5915)Time elapsed: 0.001 s
% 0.22/0.54  % (5915)------------------------------
% 0.22/0.54  % (5915)------------------------------
% 0.22/0.54  % (5888)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (5907)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (5891)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (5899)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (5902)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (5911)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (5906)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (5903)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (5897)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.55  % (5903)Refutation not found, incomplete strategy% (5903)------------------------------
% 1.38/0.55  % (5903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5895)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.55  % (5897)Refutation not found, incomplete strategy% (5897)------------------------------
% 1.38/0.55  % (5897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5914)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.55  % (5911)Refutation not found, incomplete strategy% (5911)------------------------------
% 1.38/0.55  % (5911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5903)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5903)Memory used [KB]: 1663
% 1.38/0.55  % (5903)Time elapsed: 0.151 s
% 1.38/0.55  % (5903)------------------------------
% 1.38/0.55  % (5903)------------------------------
% 1.38/0.55  % (5894)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.55  % (5897)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5897)Memory used [KB]: 6140
% 1.38/0.55  % (5897)Time elapsed: 0.152 s
% 1.38/0.55  % (5897)------------------------------
% 1.38/0.55  % (5897)------------------------------
% 1.38/0.55  % (5911)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5911)Memory used [KB]: 6140
% 1.38/0.55  % (5911)Time elapsed: 0.149 s
% 1.38/0.55  % (5911)------------------------------
% 1.38/0.55  % (5911)------------------------------
% 1.38/0.55  % (5910)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.55  % (5896)Refutation not found, incomplete strategy% (5896)------------------------------
% 1.38/0.55  % (5896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5896)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5896)Memory used [KB]: 10618
% 1.38/0.55  % (5896)Time elapsed: 0.153 s
% 1.38/0.55  % (5896)------------------------------
% 1.38/0.55  % (5896)------------------------------
% 1.38/0.55  % (5910)Refutation not found, incomplete strategy% (5910)------------------------------
% 1.38/0.55  % (5910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5910)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5910)Memory used [KB]: 10618
% 1.38/0.55  % (5910)Time elapsed: 0.147 s
% 1.38/0.55  % (5910)------------------------------
% 1.38/0.55  % (5910)------------------------------
% 1.38/0.55  % (5902)Refutation not found, incomplete strategy% (5902)------------------------------
% 1.38/0.55  % (5902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5902)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5902)Memory used [KB]: 10618
% 1.38/0.55  % (5902)Time elapsed: 0.148 s
% 1.38/0.55  % (5902)------------------------------
% 1.38/0.55  % (5902)------------------------------
% 1.38/0.56  % (5913)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.56  % (5913)Refutation not found, incomplete strategy% (5913)------------------------------
% 1.38/0.56  % (5913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (5913)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (5913)Memory used [KB]: 6140
% 1.38/0.56  % (5913)Time elapsed: 0.158 s
% 1.38/0.56  % (5913)------------------------------
% 1.38/0.56  % (5913)------------------------------
% 1.38/0.56  % (5886)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.56  % (5905)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.38/0.56  % (5914)Refutation not found, incomplete strategy% (5914)------------------------------
% 1.38/0.56  % (5914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (5914)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (5914)Memory used [KB]: 10618
% 1.38/0.56  % (5914)Time elapsed: 0.157 s
% 1.38/0.56  % (5914)------------------------------
% 1.38/0.56  % (5914)------------------------------
% 1.66/0.56  % (5904)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.66/0.57  % (5904)Refutation not found, incomplete strategy% (5904)------------------------------
% 1.66/0.57  % (5904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.57  % (5904)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.57  
% 1.66/0.57  % (5904)Memory used [KB]: 1663
% 1.66/0.57  % (5904)Time elapsed: 0.158 s
% 1.66/0.57  % (5904)------------------------------
% 1.66/0.57  % (5904)------------------------------
% 1.66/0.57  % (5909)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.66/0.57  % (5901)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.66/0.58  % (5893)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.59  % (5905)Refutation found. Thanks to Tanya!
% 1.66/0.59  % SZS status Theorem for theBenchmark
% 1.66/0.59  % SZS output start Proof for theBenchmark
% 1.66/0.59  fof(f378,plain,(
% 1.66/0.59    $false),
% 1.66/0.59    inference(resolution,[],[f319,f190])).
% 1.66/0.59  fof(f190,plain,(
% 1.66/0.59    ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1))),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f109,f80])).
% 1.66/0.59  fof(f80,plain,(
% 1.66/0.59    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k3_xboole_0(sK0,sK1))) | ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1))),
% 1.66/0.59    inference(forward_demodulation,[],[f69,f62])).
% 1.66/0.59  fof(f62,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f40,f39])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f14])).
% 1.66/0.59  fof(f14,axiom,(
% 1.66/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.66/0.59  fof(f40,plain,(
% 1.66/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f7])).
% 1.66/0.59  fof(f7,axiom,(
% 1.66/0.59    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.66/0.59  fof(f69,plain,(
% 1.66/0.59    ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1)) | ~r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1)))),
% 1.66/0.59    inference(backward_demodulation,[],[f54,f62])).
% 1.66/0.59  fof(f54,plain,(
% 1.66/0.59    ~r1_tarski(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),k6_relat_1(k3_xboole_0(sK0,sK1))) | ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))),
% 1.66/0.59    inference(extensionality_resolution,[],[f30,f27])).
% 1.66/0.59  fof(f27,plain,(
% 1.66/0.59    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.66/0.59    inference(cnf_transformation,[],[f17])).
% 1.66/0.59  fof(f17,plain,(
% 1.66/0.59    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f16])).
% 1.66/0.59  fof(f16,negated_conjecture,(
% 1.66/0.59    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.66/0.59    inference(negated_conjecture,[],[f15])).
% 1.66/0.59  fof(f15,conjecture,(
% 1.66/0.59    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.66/0.59  fof(f30,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f1])).
% 1.66/0.59  fof(f1,axiom,(
% 1.66/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.59  fof(f109,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(X0,X1)))) )),
% 1.66/0.59    inference(forward_demodulation,[],[f108,f41])).
% 1.66/0.59  fof(f41,plain,(
% 1.66/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.66/0.59    inference(cnf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.66/0.59  fof(f108,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)))) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f107,f40])).
% 1.66/0.59  fof(f107,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.66/0.59    inference(superposition,[],[f71,f33])).
% 1.66/0.59  fof(f33,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f20])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 1.66/0.59  fof(f71,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 1.66/0.59    inference(backward_demodulation,[],[f46,f62])).
% 1.66/0.59  fof(f46,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f40,f37])).
% 1.66/0.59  fof(f37,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f25])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f12])).
% 1.66/0.59  fof(f12,axiom,(
% 1.66/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.66/0.59  fof(f319,plain,(
% 1.66/0.59    ( ! [X4,X5] : (r1_tarski(k6_relat_1(k3_xboole_0(X4,X5)),k7_relat_1(k6_relat_1(X4),X5))) )),
% 1.66/0.59    inference(superposition,[],[f167,f196])).
% 1.66/0.59  fof(f196,plain,(
% 1.66/0.59    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.66/0.59    inference(superposition,[],[f62,f103])).
% 1.66/0.59  fof(f103,plain,(
% 1.66/0.59    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.66/0.59    inference(forward_demodulation,[],[f99,f41])).
% 1.66/0.59  fof(f99,plain,(
% 1.66/0.59    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0))) )),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f40,f43,f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f24,plain,(
% 1.66/0.59    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(flattening,[],[f23])).
% 1.66/0.59  fof(f23,plain,(
% 1.66/0.59    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f13])).
% 1.66/0.59  fof(f13,axiom,(
% 1.66/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.59    inference(equality_resolution,[],[f29])).
% 1.66/0.59  fof(f29,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f1])).
% 1.66/0.59  fof(f167,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)),k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.66/0.59    inference(backward_demodulation,[],[f72,f161])).
% 1.66/0.59  fof(f161,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0))) )),
% 1.66/0.59    inference(forward_demodulation,[],[f160,f62])).
% 1.66/0.59  fof(f160,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0))) )),
% 1.66/0.59    inference(forward_demodulation,[],[f159,f119])).
% 1.66/0.59  fof(f119,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X0,X2))) )),
% 1.66/0.59    inference(backward_demodulation,[],[f77,f110])).
% 1.66/0.59  fof(f110,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))) )),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f40,f32])).
% 1.66/0.59  fof(f32,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f19])).
% 1.66/0.59  fof(f19,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.66/0.59    inference(ennf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 1.66/0.59  fof(f77,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.66/0.59    inference(backward_demodulation,[],[f63,f62])).
% 1.66/0.59  fof(f63,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f45,f39])).
% 1.66/0.59  fof(f45,plain,(
% 1.66/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f40,f40,f35])).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f22])).
% 1.66/0.59  fof(f22,plain,(
% 1.66/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.66/0.59    inference(flattening,[],[f21])).
% 1.66/0.59  fof(f21,plain,(
% 1.66/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.66/0.59    inference(ennf_transformation,[],[f6])).
% 1.66/0.59  fof(f6,axiom,(
% 1.66/0.59    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.66/0.59  fof(f159,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.66/0.59    inference(forward_demodulation,[],[f126,f62])).
% 1.66/0.59  fof(f126,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f40,f40,f40,f31])).
% 1.66/0.59  fof(f31,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.59    inference(ennf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.66/0.59  fof(f72,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.66/0.59    inference(backward_demodulation,[],[f47,f62])).
% 1.66/0.59  fof(f47,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f45,f37])).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (5905)------------------------------
% 1.66/0.59  % (5905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (5905)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (5905)Memory used [KB]: 1918
% 1.66/0.59  % (5905)Time elapsed: 0.190 s
% 1.66/0.59  % (5905)------------------------------
% 1.66/0.59  % (5905)------------------------------
% 1.66/0.59  % (5885)Success in time 0.235 s
%------------------------------------------------------------------------------
