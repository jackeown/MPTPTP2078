%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  75 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 280 expanded)
%              Number of equality atoms :   19 (  47 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(subsumption_resolution,[],[f76,f54])).

fof(f54,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(subsumption_resolution,[],[f53,f47])).

fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tarski(X0))
      | r2_hidden(X0,k1_tarski(X0)) ) ),
    inference(resolution,[],[f52,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f52,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f41,f38])).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f43,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f76,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f75,f34])).

fof(f34,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f74,f31])).

fof(f31,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
      | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f73,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | k1_xboole_0 = sK1
      | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
      | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK2,X2,X0)
      | r2_hidden(k1_funct_1(sK2,X1),X0) ) ),
    inference(resolution,[],[f46,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:18:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.57  % (26026)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.57  % (26025)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.57  % (26025)Refutation found. Thanks to Tanya!
% 0.23/0.57  % SZS status Theorem for theBenchmark
% 0.23/0.58  % (26026)Refutation not found, incomplete strategy% (26026)------------------------------
% 0.23/0.58  % (26026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (26034)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.58  % (26041)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.58  % (26026)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (26026)Memory used [KB]: 10618
% 0.23/0.58  % (26026)Time elapsed: 0.124 s
% 0.23/0.58  % (26026)------------------------------
% 0.23/0.58  % (26026)------------------------------
% 0.23/0.58  % (26042)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.58  % (26033)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.58  % SZS output start Proof for theBenchmark
% 0.23/0.58  fof(f78,plain,(
% 0.23/0.58    $false),
% 0.23/0.58    inference(subsumption_resolution,[],[f76,f54])).
% 0.23/0.58  fof(f54,plain,(
% 0.23/0.58    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f53,f47])).
% 0.23/0.58  fof(f47,plain,(
% 0.23/0.58    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.23/0.58    inference(superposition,[],[f37,f35])).
% 0.23/0.58  fof(f35,plain,(
% 0.23/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f3])).
% 0.23/0.58  fof(f3,axiom,(
% 0.23/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.58  fof(f37,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.23/0.58    inference(cnf_transformation,[],[f7])).
% 0.23/0.58  fof(f7,axiom,(
% 0.23/0.58    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.23/0.58  fof(f53,plain,(
% 0.23/0.58    ( ! [X0] : (v1_xboole_0(k1_tarski(X0)) | r2_hidden(X0,k1_tarski(X0))) )),
% 0.23/0.58    inference(resolution,[],[f52,f42])).
% 0.23/0.58  fof(f42,plain,(
% 0.23/0.58    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f19])).
% 0.23/0.58  fof(f19,plain,(
% 0.23/0.58    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.23/0.58    inference(ennf_transformation,[],[f8])).
% 0.23/0.58  fof(f8,axiom,(
% 0.23/0.58    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.23/0.58  fof(f52,plain,(
% 0.23/0.58    ( ! [X2] : (~r1_xboole_0(X2,X2) | v1_xboole_0(X2)) )),
% 0.23/0.58    inference(resolution,[],[f49,f48])).
% 0.23/0.58  fof(f48,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 0.23/0.58    inference(superposition,[],[f41,f38])).
% 0.23/0.58  fof(f38,plain,(
% 0.23/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.23/0.58    inference(cnf_transformation,[],[f14])).
% 0.23/0.58  fof(f14,plain,(
% 0.23/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.23/0.58    inference(rectify,[],[f1])).
% 0.23/0.58  fof(f1,axiom,(
% 0.23/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.23/0.58  fof(f41,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f29])).
% 0.23/0.58  fof(f29,plain,(
% 0.23/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f28])).
% 0.23/0.58  fof(f28,plain,(
% 0.23/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f18,plain,(
% 0.23/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.58    inference(ennf_transformation,[],[f15])).
% 0.23/0.58  fof(f15,plain,(
% 0.23/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.58    inference(rectify,[],[f2])).
% 0.23/0.58  fof(f2,axiom,(
% 0.23/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.23/0.58  fof(f49,plain,(
% 0.23/0.58    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.23/0.58    inference(resolution,[],[f43,f36])).
% 0.23/0.58  fof(f36,plain,(
% 0.23/0.58    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f27])).
% 0.23/0.58  fof(f27,plain,(
% 0.23/0.58    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 0.23/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f26])).
% 0.23/0.58  fof(f26,plain,(
% 0.23/0.58    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f9,axiom,(
% 0.23/0.58    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.23/0.58  fof(f43,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f21])).
% 0.23/0.58  fof(f21,plain,(
% 0.23/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.58    inference(flattening,[],[f20])).
% 0.23/0.58  fof(f20,plain,(
% 0.23/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.58    inference(ennf_transformation,[],[f10])).
% 0.23/0.58  fof(f10,axiom,(
% 0.23/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.58  fof(f76,plain,(
% 0.23/0.58    ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.23/0.58    inference(resolution,[],[f75,f34])).
% 0.23/0.58  fof(f34,plain,(
% 0.23/0.58    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.23/0.58    inference(cnf_transformation,[],[f25])).
% 0.23/0.58  fof(f25,plain,(
% 0.23/0.58    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.23/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f24])).
% 0.23/0.58  fof(f24,plain,(
% 0.23/0.58    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f17,plain,(
% 0.23/0.58    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.23/0.58    inference(flattening,[],[f16])).
% 0.23/0.58  fof(f16,plain,(
% 0.23/0.58    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.23/0.58    inference(ennf_transformation,[],[f13])).
% 0.23/0.58  fof(f13,negated_conjecture,(
% 0.23/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.23/0.58    inference(negated_conjecture,[],[f12])).
% 0.23/0.58  fof(f12,conjecture,(
% 0.23/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.23/0.58  fof(f75,plain,(
% 0.23/0.58    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f74,f31])).
% 0.23/0.58  fof(f31,plain,(
% 0.23/0.58    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.23/0.58    inference(cnf_transformation,[],[f25])).
% 0.23/0.58  fof(f74,plain,(
% 0.23/0.58    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | r2_hidden(k1_funct_1(sK2,X0),sK1)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f73,f33])).
% 0.23/0.58  fof(f33,plain,(
% 0.23/0.58    k1_xboole_0 != sK1),
% 0.23/0.58    inference(cnf_transformation,[],[f25])).
% 0.23/0.58  fof(f73,plain,(
% 0.23/0.58    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | r2_hidden(k1_funct_1(sK2,X0),sK1)) )),
% 0.23/0.58    inference(resolution,[],[f72,f32])).
% 0.23/0.58  fof(f32,plain,(
% 0.23/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.23/0.58    inference(cnf_transformation,[],[f25])).
% 0.23/0.58  fof(f72,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK2,X2,X0) | r2_hidden(k1_funct_1(sK2,X1),X0)) )),
% 0.23/0.58    inference(resolution,[],[f46,f30])).
% 0.23/0.58  fof(f30,plain,(
% 0.23/0.58    v1_funct_1(sK2)),
% 0.23/0.58    inference(cnf_transformation,[],[f25])).
% 0.23/0.58  fof(f46,plain,(
% 0.23/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f23])).
% 0.23/0.58  fof(f23,plain,(
% 0.23/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.23/0.58    inference(flattening,[],[f22])).
% 0.23/0.58  fof(f22,plain,(
% 0.23/0.58    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.23/0.58    inference(ennf_transformation,[],[f11])).
% 0.23/0.58  fof(f11,axiom,(
% 0.23/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.23/0.58  % SZS output end Proof for theBenchmark
% 0.23/0.58  % (26025)------------------------------
% 0.23/0.58  % (26025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (26025)Termination reason: Refutation
% 0.23/0.58  
% 0.23/0.58  % (26025)Memory used [KB]: 6268
% 0.23/0.58  % (26025)Time elapsed: 0.125 s
% 0.23/0.58  % (26025)------------------------------
% 0.23/0.58  % (26025)------------------------------
% 0.23/0.59  % (26017)Success in time 0.211 s
%------------------------------------------------------------------------------
