%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:27 EST 2020

% Result     : Theorem 2.71s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 169 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 286 expanded)
%              Number of equality atoms :   43 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2009,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f571,f85,f681,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f681,plain,(
    ! [X2,X3] : r1_tarski(k6_relat_1(k3_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f300,f144])).

fof(f144,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f84,f74])).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f73,f43])).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f84,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f52,f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f300,plain,(
    ! [X14,X12,X13] : r1_tarski(k7_relat_1(k6_relat_1(X14),k3_xboole_0(X12,X13)),k7_relat_1(k6_relat_1(X12),X13)) ),
    inference(backward_demodulation,[],[f105,f297])).

fof(f297,plain,(
    ! [X2,X0,X1] : k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f296,f84])).

fof(f296,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f294,f112])).

fof(f112,plain,(
    ! [X6,X8,X7] : k5_relat_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X7),X8)) = k7_relat_1(k6_relat_1(X7),k3_xboole_0(X8,X6)) ),
    inference(forward_demodulation,[],[f103,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2)) ),
    inference(resolution,[],[f63,f41])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f103,plain,(
    ! [X6,X8,X7] : k5_relat_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X7),X8)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),X8),X6) ),
    inference(resolution,[],[f89,f52])).

fof(f89,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f88,f84])).

fof(f88,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(resolution,[],[f72,f41])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f58,f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f294,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f158,f41])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f156,f84])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f98,f41])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f105,plain,(
    ! [X14,X12,X13] : r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X12),X13),k6_relat_1(X14)),k7_relat_1(k6_relat_1(X12),X13)) ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f85,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f40,f84])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f36])).

fof(f36,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f571,plain,(
    ! [X4,X5] : r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(k3_xboole_0(X4,X5))) ),
    inference(superposition,[],[f87,f159])).

fof(f159,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f97,f144])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f68,f84])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f54,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (9565)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (9579)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.50  % (9581)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (9563)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (9581)Refutation not found, incomplete strategy% (9581)------------------------------
% 0.21/0.50  % (9581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9581)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9581)Memory used [KB]: 6140
% 0.21/0.50  % (9581)Time elapsed: 0.093 s
% 0.21/0.50  % (9581)------------------------------
% 0.21/0.50  % (9581)------------------------------
% 0.21/0.50  % (9559)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (9573)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (9579)Refutation not found, incomplete strategy% (9579)------------------------------
% 0.21/0.51  % (9579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9579)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9579)Memory used [KB]: 10618
% 0.21/0.51  % (9579)Time elapsed: 0.092 s
% 0.21/0.51  % (9579)------------------------------
% 0.21/0.51  % (9579)------------------------------
% 0.21/0.51  % (9573)Refutation not found, incomplete strategy% (9573)------------------------------
% 0.21/0.51  % (9573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9573)Memory used [KB]: 1663
% 0.21/0.51  % (9573)Time elapsed: 0.103 s
% 0.21/0.51  % (9573)------------------------------
% 0.21/0.51  % (9573)------------------------------
% 0.21/0.51  % (9565)Refutation not found, incomplete strategy% (9565)------------------------------
% 0.21/0.51  % (9565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9565)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9565)Memory used [KB]: 10618
% 0.21/0.51  % (9565)Time elapsed: 0.103 s
% 0.21/0.51  % (9565)------------------------------
% 0.21/0.51  % (9565)------------------------------
% 0.21/0.52  % (9577)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (9558)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (9560)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (9571)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (9555)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (9556)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (9556)Refutation not found, incomplete strategy% (9556)------------------------------
% 0.21/0.53  % (9556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9556)Memory used [KB]: 1663
% 0.21/0.53  % (9556)Time elapsed: 0.122 s
% 0.21/0.53  % (9556)------------------------------
% 0.21/0.53  % (9556)------------------------------
% 0.21/0.53  % (9583)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (9557)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (9583)Refutation not found, incomplete strategy% (9583)------------------------------
% 0.21/0.54  % (9583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9583)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9583)Memory used [KB]: 10618
% 0.21/0.54  % (9583)Time elapsed: 0.139 s
% 0.21/0.54  % (9583)------------------------------
% 0.21/0.54  % (9583)------------------------------
% 0.21/0.54  % (9584)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (9582)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (9575)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (9584)Refutation not found, incomplete strategy% (9584)------------------------------
% 0.21/0.54  % (9584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9584)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9584)Memory used [KB]: 1663
% 0.21/0.54  % (9584)Time elapsed: 0.001 s
% 0.21/0.54  % (9584)------------------------------
% 0.21/0.54  % (9584)------------------------------
% 0.21/0.54  % (9582)Refutation not found, incomplete strategy% (9582)------------------------------
% 0.21/0.54  % (9582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9582)Memory used [KB]: 6140
% 0.21/0.54  % (9582)Time elapsed: 0.136 s
% 0.21/0.54  % (9582)------------------------------
% 0.21/0.54  % (9582)------------------------------
% 0.21/0.54  % (9569)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (9576)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (9574)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (9567)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (9567)Refutation not found, incomplete strategy% (9567)------------------------------
% 0.21/0.54  % (9567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9567)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9567)Memory used [KB]: 10618
% 0.21/0.54  % (9567)Time elapsed: 0.141 s
% 0.21/0.54  % (9567)------------------------------
% 0.21/0.54  % (9567)------------------------------
% 0.21/0.55  % (9564)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (9578)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (9570)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (9568)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (9580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (9566)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (9569)Refutation not found, incomplete strategy% (9569)------------------------------
% 0.21/0.55  % (9569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9569)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9569)Memory used [KB]: 1663
% 0.21/0.55  % (9569)Time elapsed: 0.109 s
% 0.21/0.55  % (9569)------------------------------
% 0.21/0.55  % (9569)------------------------------
% 0.21/0.55  % (9580)Refutation not found, incomplete strategy% (9580)------------------------------
% 0.21/0.55  % (9580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9580)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9580)Memory used [KB]: 6140
% 0.21/0.55  % (9580)Time elapsed: 0.146 s
% 0.21/0.55  % (9580)------------------------------
% 0.21/0.55  % (9580)------------------------------
% 0.21/0.55  % (9566)Refutation not found, incomplete strategy% (9566)------------------------------
% 0.21/0.55  % (9566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9566)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9566)Memory used [KB]: 6140
% 0.21/0.55  % (9566)Time elapsed: 0.146 s
% 0.21/0.55  % (9566)------------------------------
% 0.21/0.55  % (9566)------------------------------
% 0.21/0.55  % (9561)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (9571)Refutation not found, incomplete strategy% (9571)------------------------------
% 0.21/0.55  % (9571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9571)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9571)Memory used [KB]: 10618
% 0.21/0.55  % (9571)Time elapsed: 0.146 s
% 0.21/0.55  % (9571)------------------------------
% 0.21/0.55  % (9571)------------------------------
% 0.21/0.56  % (9572)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (9572)Refutation not found, incomplete strategy% (9572)------------------------------
% 0.21/0.56  % (9572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9572)Memory used [KB]: 1663
% 0.21/0.56  % (9572)Time elapsed: 0.155 s
% 0.21/0.56  % (9572)------------------------------
% 0.21/0.56  % (9572)------------------------------
% 0.21/0.56  % (9562)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.59  % (9563)Refutation not found, incomplete strategy% (9563)------------------------------
% 0.21/0.59  % (9563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (9563)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (9563)Memory used [KB]: 6140
% 0.21/0.59  % (9563)Time elapsed: 0.184 s
% 0.21/0.59  % (9563)------------------------------
% 0.21/0.59  % (9563)------------------------------
% 1.96/0.61  % (9585)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.96/0.61  % (9589)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.96/0.61  % (9589)Refutation not found, incomplete strategy% (9589)------------------------------
% 1.96/0.61  % (9589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.61  % (9589)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.61  
% 1.96/0.61  % (9589)Memory used [KB]: 10618
% 1.96/0.61  % (9589)Time elapsed: 0.040 s
% 1.96/0.61  % (9589)------------------------------
% 1.96/0.61  % (9589)------------------------------
% 2.12/0.64  % (9587)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.12/0.65  % (9586)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.12/0.65  % (9599)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.12/0.66  % (9588)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.12/0.66  % (9588)Refutation not found, incomplete strategy% (9588)------------------------------
% 2.12/0.66  % (9588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.66  % (9588)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.66  
% 2.12/0.66  % (9588)Memory used [KB]: 10618
% 2.12/0.66  % (9588)Time elapsed: 0.063 s
% 2.12/0.66  % (9588)------------------------------
% 2.12/0.66  % (9588)------------------------------
% 2.12/0.67  % (9558)Refutation not found, incomplete strategy% (9558)------------------------------
% 2.12/0.67  % (9558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.67  % (9558)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.67  
% 2.12/0.67  % (9558)Memory used [KB]: 6140
% 2.12/0.67  % (9558)Time elapsed: 0.254 s
% 2.12/0.67  % (9558)------------------------------
% 2.12/0.67  % (9558)------------------------------
% 2.12/0.67  % (9557)Refutation not found, incomplete strategy% (9557)------------------------------
% 2.12/0.67  % (9557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.67  % (9557)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.67  
% 2.12/0.67  % (9557)Memory used [KB]: 6140
% 2.12/0.67  % (9557)Time elapsed: 0.264 s
% 2.12/0.67  % (9557)------------------------------
% 2.12/0.67  % (9557)------------------------------
% 2.12/0.67  % (9592)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.12/0.68  % (9590)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.12/0.68  % (9595)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.12/0.68  % (9593)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.12/0.69  % (9597)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.12/0.69  % (9596)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.12/0.69  % (9591)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.12/0.69  % (9591)Refutation not found, incomplete strategy% (9591)------------------------------
% 2.12/0.69  % (9591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.69  % (9591)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.69  
% 2.12/0.69  % (9591)Memory used [KB]: 10618
% 2.12/0.69  % (9591)Time elapsed: 0.120 s
% 2.12/0.69  % (9591)------------------------------
% 2.12/0.69  % (9591)------------------------------
% 2.12/0.70  % (9600)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.12/0.70  % (9596)Refutation not found, incomplete strategy% (9596)------------------------------
% 2.12/0.70  % (9596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.70  % (9596)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.70  
% 2.12/0.70  % (9596)Memory used [KB]: 10618
% 2.12/0.70  % (9596)Time elapsed: 0.114 s
% 2.12/0.70  % (9596)------------------------------
% 2.12/0.70  % (9596)------------------------------
% 2.12/0.70  % (9590)Refutation not found, incomplete strategy% (9590)------------------------------
% 2.12/0.70  % (9590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.70  % (9590)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.70  
% 2.12/0.70  % (9590)Memory used [KB]: 1663
% 2.12/0.70  % (9590)Time elapsed: 0.132 s
% 2.12/0.70  % (9590)------------------------------
% 2.12/0.70  % (9590)------------------------------
% 2.71/0.71  % (9570)Refutation not found, incomplete strategy% (9570)------------------------------
% 2.71/0.71  % (9570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.71  % (9570)Termination reason: Refutation not found, incomplete strategy
% 2.71/0.71  
% 2.71/0.71  % (9570)Memory used [KB]: 6140
% 2.71/0.71  % (9570)Time elapsed: 0.288 s
% 2.71/0.71  % (9570)------------------------------
% 2.71/0.71  % (9570)------------------------------
% 2.71/0.71  % (9598)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.71/0.73  % (9594)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.71/0.73  % (9594)Refutation not found, incomplete strategy% (9594)------------------------------
% 2.71/0.73  % (9594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.73  % (9594)Termination reason: Refutation not found, incomplete strategy
% 2.71/0.73  
% 2.71/0.73  % (9594)Memory used [KB]: 10618
% 2.71/0.73  % (9594)Time elapsed: 0.148 s
% 2.71/0.73  % (9594)------------------------------
% 2.71/0.73  % (9594)------------------------------
% 2.71/0.73  % (9598)Refutation not found, incomplete strategy% (9598)------------------------------
% 2.71/0.73  % (9598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.73  % (9598)Termination reason: Refutation not found, incomplete strategy
% 2.71/0.73  
% 2.71/0.73  % (9598)Memory used [KB]: 10618
% 2.71/0.73  % (9598)Time elapsed: 0.119 s
% 2.71/0.73  % (9598)------------------------------
% 2.71/0.73  % (9598)------------------------------
% 2.71/0.73  % (9562)Refutation found. Thanks to Tanya!
% 2.71/0.73  % SZS status Theorem for theBenchmark
% 2.71/0.73  % SZS output start Proof for theBenchmark
% 2.71/0.73  fof(f2009,plain,(
% 2.71/0.73    $false),
% 2.71/0.73    inference(unit_resulting_resolution,[],[f571,f85,f681,f61])).
% 2.71/0.73  fof(f61,plain,(
% 2.71/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.71/0.73    inference(cnf_transformation,[],[f39])).
% 2.71/0.73  fof(f39,plain,(
% 2.71/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.71/0.73    inference(flattening,[],[f38])).
% 2.71/0.73  fof(f38,plain,(
% 2.71/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.71/0.73    inference(nnf_transformation,[],[f2])).
% 2.71/0.73  fof(f2,axiom,(
% 2.71/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.71/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.71/0.73  fof(f681,plain,(
% 2.71/0.73    ( ! [X2,X3] : (r1_tarski(k6_relat_1(k3_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),X3))) )),
% 2.71/0.73    inference(superposition,[],[f300,f144])).
% 2.71/0.73  fof(f144,plain,(
% 2.71/0.73    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 2.71/0.73    inference(superposition,[],[f84,f74])).
% 2.71/0.73  fof(f74,plain,(
% 2.71/0.73    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 2.71/0.73    inference(forward_demodulation,[],[f73,f43])).
% 2.71/0.73  fof(f43,plain,(
% 2.71/0.73    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.71/0.73    inference(cnf_transformation,[],[f12])).
% 2.71/0.73  fof(f12,axiom,(
% 2.71/0.73    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.71/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.71/0.73  fof(f73,plain,(
% 2.71/0.73    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 2.71/0.73    inference(resolution,[],[f44,f41])).
% 2.71/0.73  fof(f41,plain,(
% 2.71/0.73    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.71/0.73    inference(cnf_transformation,[],[f22])).
% 2.71/0.73  fof(f22,plain,(
% 2.71/0.73    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.71/0.73    inference(pure_predicate_removal,[],[f19])).
% 2.71/0.73  fof(f19,axiom,(
% 2.71/0.73    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.71/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.71/0.73  fof(f44,plain,(
% 2.71/0.73    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.71/0.73    inference(cnf_transformation,[],[f24])).
% 2.71/0.73  fof(f24,plain,(
% 2.71/0.73    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.71/0.73    inference(ennf_transformation,[],[f15])).
% 2.71/0.73  fof(f15,axiom,(
% 2.71/0.73    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.71/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.71/0.73  fof(f84,plain,(
% 2.71/0.73    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 2.71/0.73    inference(resolution,[],[f52,f41])).
% 2.71/0.73  fof(f52,plain,(
% 2.71/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 2.71/0.73    inference(cnf_transformation,[],[f26])).
% 2.71/0.73  fof(f26,plain,(
% 2.71/0.73    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.71/0.73    inference(ennf_transformation,[],[f17])).
% 2.71/0.73  fof(f17,axiom,(
% 2.71/0.73    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 2.71/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.71/0.73  fof(f300,plain,(
% 2.71/0.73    ( ! [X14,X12,X13] : (r1_tarski(k7_relat_1(k6_relat_1(X14),k3_xboole_0(X12,X13)),k7_relat_1(k6_relat_1(X12),X13))) )),
% 2.71/0.73    inference(backward_demodulation,[],[f105,f297])).
% 2.71/0.73  fof(f297,plain,(
% 2.71/0.73    ( ! [X2,X0,X1] : (k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 2.71/0.73    inference(forward_demodulation,[],[f296,f84])).
% 2.71/0.73  fof(f296,plain,(
% 2.71/0.73    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0))) )),
% 2.71/0.73    inference(forward_demodulation,[],[f294,f112])).
% 2.71/0.74  fof(f112,plain,(
% 2.71/0.74    ( ! [X6,X8,X7] : (k5_relat_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X7),X8)) = k7_relat_1(k6_relat_1(X7),k3_xboole_0(X8,X6))) )),
% 2.71/0.74    inference(forward_demodulation,[],[f103,f97])).
% 2.71/0.74  fof(f97,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))) )),
% 2.71/0.74    inference(resolution,[],[f63,f41])).
% 2.71/0.74  fof(f63,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 2.71/0.74    inference(cnf_transformation,[],[f35])).
% 2.71/0.74  fof(f35,plain,(
% 2.71/0.74    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.71/0.74    inference(ennf_transformation,[],[f10])).
% 2.71/0.74  fof(f10,axiom,(
% 2.71/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 2.71/0.74  fof(f103,plain,(
% 2.71/0.74    ( ! [X6,X8,X7] : (k5_relat_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X7),X8)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),X8),X6)) )),
% 2.71/0.74    inference(resolution,[],[f89,f52])).
% 2.71/0.74  fof(f89,plain,(
% 2.71/0.74    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.71/0.74    inference(forward_demodulation,[],[f88,f84])).
% 2.71/0.74  fof(f88,plain,(
% 2.71/0.74    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 2.71/0.74    inference(resolution,[],[f72,f41])).
% 2.71/0.74  fof(f72,plain,(
% 2.71/0.74    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))) )),
% 2.71/0.74    inference(resolution,[],[f58,f41])).
% 2.71/0.74  fof(f58,plain,(
% 2.71/0.74    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f34])).
% 2.71/0.74  fof(f34,plain,(
% 2.71/0.74    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.71/0.74    inference(flattening,[],[f33])).
% 2.71/0.74  fof(f33,plain,(
% 2.71/0.74    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.71/0.74    inference(ennf_transformation,[],[f9])).
% 2.71/0.74  fof(f9,axiom,(
% 2.71/0.74    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.71/0.74  fof(f294,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.71/0.74    inference(resolution,[],[f158,f41])).
% 2.71/0.74  fof(f158,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.71/0.74    inference(forward_demodulation,[],[f156,f84])).
% 2.71/0.74  fof(f156,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.71/0.74    inference(resolution,[],[f98,f41])).
% 2.71/0.74  fof(f98,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.71/0.74    inference(resolution,[],[f45,f41])).
% 2.71/0.74  fof(f45,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f25])).
% 2.71/0.74  fof(f25,plain,(
% 2.71/0.74    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.71/0.74    inference(ennf_transformation,[],[f11])).
% 2.71/0.74  fof(f11,axiom,(
% 2.71/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.71/0.74  fof(f105,plain,(
% 2.71/0.74    ( ! [X14,X12,X13] : (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X12),X13),k6_relat_1(X14)),k7_relat_1(k6_relat_1(X12),X13))) )),
% 2.71/0.74    inference(resolution,[],[f89,f54])).
% 2.71/0.74  fof(f54,plain,(
% 2.71/0.74    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f28])).
% 2.71/0.74  fof(f28,plain,(
% 2.71/0.74    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 2.71/0.74    inference(ennf_transformation,[],[f13])).
% 2.71/0.74  fof(f13,axiom,(
% 2.71/0.74    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 2.71/0.74  fof(f85,plain,(
% 2.71/0.74    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.71/0.74    inference(backward_demodulation,[],[f40,f84])).
% 2.71/0.74  fof(f40,plain,(
% 2.71/0.74    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.71/0.74    inference(cnf_transformation,[],[f37])).
% 2.71/0.74  fof(f37,plain,(
% 2.71/0.74    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.71/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f36])).
% 2.71/0.74  fof(f36,plain,(
% 2.71/0.74    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.71/0.74    introduced(choice_axiom,[])).
% 2.71/0.74  fof(f23,plain,(
% 2.71/0.74    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.71/0.74    inference(ennf_transformation,[],[f21])).
% 2.71/0.74  fof(f21,negated_conjecture,(
% 2.71/0.74    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.71/0.74    inference(negated_conjecture,[],[f20])).
% 2.71/0.74  fof(f20,conjecture,(
% 2.71/0.74    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.71/0.74  fof(f571,plain,(
% 2.71/0.74    ( ! [X4,X5] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(k3_xboole_0(X4,X5)))) )),
% 2.71/0.74    inference(superposition,[],[f87,f159])).
% 2.71/0.74  fof(f159,plain,(
% 2.71/0.74    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 2.71/0.74    inference(superposition,[],[f97,f144])).
% 2.71/0.74  fof(f87,plain,(
% 2.71/0.74    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 2.71/0.74    inference(backward_demodulation,[],[f68,f84])).
% 2.71/0.74  fof(f68,plain,(
% 2.71/0.74    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 2.71/0.74    inference(resolution,[],[f54,f41])).
% 2.71/0.74  % SZS output end Proof for theBenchmark
% 2.71/0.74  % (9562)------------------------------
% 2.71/0.74  % (9562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.74  % (9562)Termination reason: Refutation
% 2.71/0.74  
% 2.71/0.74  % (9562)Memory used [KB]: 3326
% 2.71/0.74  % (9562)Time elapsed: 0.333 s
% 2.71/0.74  % (9562)------------------------------
% 2.71/0.74  % (9562)------------------------------
% 2.71/0.74  % (9554)Success in time 0.374 s
%------------------------------------------------------------------------------
