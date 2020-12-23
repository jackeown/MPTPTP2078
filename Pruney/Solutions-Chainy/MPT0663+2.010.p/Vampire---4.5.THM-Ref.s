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
% DateTime   : Thu Dec  3 12:53:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  38 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 ( 117 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f24,f14])).

fof(f14,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(f24,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    inference(resolution,[],[f23,f13])).

fof(f13,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1))
      | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0) ) ),
    inference(forward_demodulation,[],[f22,f20])).

fof(f20,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0) ),
    inference(resolution,[],[f16,f11])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f21,f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0) ) ),
    inference(resolution,[],[f17,f12])).

fof(f12,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:11:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (5952)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.42  % (5953)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (5952)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f24,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)),
% 0.21/0.42    inference(resolution,[],[f23,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1)) | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f22,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)) )),
% 0.21/0.42    inference(resolution,[],[f16,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f21,f11])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0)) )),
% 0.21/0.42    inference(resolution,[],[f17,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    v1_funct_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (5952)------------------------------
% 0.21/0.42  % (5952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (5952)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (5952)Memory used [KB]: 10490
% 0.21/0.42  % (5952)Time elapsed: 0.004 s
% 0.21/0.42  % (5952)------------------------------
% 0.21/0.42  % (5952)------------------------------
% 0.21/0.42  % (5948)Success in time 0.064 s
%------------------------------------------------------------------------------
