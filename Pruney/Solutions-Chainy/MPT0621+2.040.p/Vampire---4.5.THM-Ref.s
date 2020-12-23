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
% DateTime   : Thu Dec  3 12:52:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 241 expanded)
%              Number of leaves         :    8 (  57 expanded)
%              Depth                    :   21
%              Number of atoms          :  136 ( 897 expanded)
%              Number of equality atoms :   79 ( 472 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f230,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f81])).

fof(f81,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f79,f79])).

fof(f79,plain,(
    ! [X0] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0 ),
    inference(subsumption_resolution,[],[f78,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0 ) ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK0
      | k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0 ) ),
    inference(superposition,[],[f68,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f68,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,k1_enumset1(sK2(X1,sK0),sK2(X1,sK0),sK2(X1,sK0))) != X1
      | sK0 = X1
      | k1_funct_1(sK1(sK0),sK2(X1,sK0)) = X2 ) ),
    inference(resolution,[],[f56,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,sK0),X0)
      | k1_funct_1(sK1(sK0),sK2(X0,sK0)) = X1
      | sK0 = X0 ) ),
    inference(resolution,[],[f52,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f52,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1(sK0),X3) = X2 ) ),
    inference(superposition,[],[f28,f50])).

fof(f50,plain,(
    ! [X0] : sK1(sK0) = sK3(sK0,X0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0) = sK3(sK0,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK0 != X2
      | sK3(X0,X1) = sK1(X2) ) ),
    inference(superposition,[],[f44,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f44,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK3(X2,X3))
      | sK0 != X4
      | sK3(X2,X3) = sK1(X4) ) ),
    inference(subsumption_resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(sK3(X2,X3))
      | sK0 != X4
      | sK0 != k1_relat_1(sK3(X2,X3))
      | sK3(X2,X3) = sK1(X4) ) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK0 != X0
      | k1_relat_1(X1) != sK0
      | sK1(X0) = X1 ) ),
    inference(forward_demodulation,[],[f37,f22])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | sK0 != k1_relat_1(sK1(X0))
      | k1_relat_1(X1) != sK0
      | sK1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f35,f20])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | sK0 != k1_relat_1(sK1(X0))
      | k1_relat_1(X1) != sK0
      | sK1(X0) = X1 ) ),
    inference(resolution,[],[f15,f21])).

fof(f21,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | k1_relat_1(X2) != sK0
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK3(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f139,plain,(
    ! [X0] : k1_xboole_0 != X0 ),
    inference(superposition,[],[f16,f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (3598)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.48  % (3598)Refutation not found, incomplete strategy% (3598)------------------------------
% 0.21/0.48  % (3598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3598)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3598)Memory used [KB]: 1663
% 0.21/0.49  % (3598)Time elapsed: 0.072 s
% 0.21/0.49  % (3598)------------------------------
% 0.21/0.49  % (3598)------------------------------
% 0.21/0.49  % (3607)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.49  % (3607)Refutation not found, incomplete strategy% (3607)------------------------------
% 0.21/0.49  % (3607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3623)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (3621)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (3619)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (3615)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (3607)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3607)Memory used [KB]: 10618
% 0.21/0.51  % (3607)Time elapsed: 0.086 s
% 0.21/0.51  % (3607)------------------------------
% 0.21/0.51  % (3607)------------------------------
% 0.21/0.51  % (3619)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 = X1) )),
% 0.21/0.51    inference(superposition,[],[f79,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK0 | k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0) )),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0) )),
% 0.21/0.51    inference(superposition,[],[f68,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k4_xboole_0(X1,k1_enumset1(sK2(X1,sK0),sK2(X1,sK0),sK2(X1,sK0))) != X1 | sK0 = X1 | k1_funct_1(sK1(sK0),sK2(X1,sK0)) = X2) )),
% 0.21/0.51    inference(resolution,[],[f56,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f27,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f18,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,sK0),X0) | k1_funct_1(sK1(sK0),sK2(X0,sK0)) = X1 | sK0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f52,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(X3,sK0) | k1_funct_1(sK1(sK0),X3) = X2) )),
% 0.21/0.51    inference(superposition,[],[f28,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (sK1(sK0) = sK3(sK0,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sK0 != X0 | sK1(X0) = sK3(sK0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sK0 != X0 | sK0 != X2 | sK3(X0,X1) = sK1(X2)) )),
% 0.21/0.51    inference(superposition,[],[f44,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK3(X2,X3)) | sK0 != X4 | sK3(X2,X3) = sK1(X4)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f42,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~v1_relat_1(sK3(X2,X3)) | sK0 != X4 | sK0 != k1_relat_1(sK3(X2,X3)) | sK3(X2,X3) = sK1(X4)) )),
% 0.21/0.51    inference(resolution,[],[f38,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | sK0 != X0 | k1_relat_1(X1) != sK0 | sK1(X0) = X1) )),
% 0.21/0.51    inference(forward_demodulation,[],[f37,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | sK0 != k1_relat_1(sK1(X0)) | k1_relat_1(X1) != sK0 | sK1(X0) = X1) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f35,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(sK1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | sK0 != k1_relat_1(sK1(X0)) | k1_relat_1(X1) != sK0 | sK1(X0) = X1) )),
% 0.21/0.51    inference(resolution,[],[f15,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | k1_relat_1(X2) != sK0 | X1 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != X0) )),
% 0.21/0.51    inference(superposition,[],[f16,f81])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (3619)------------------------------
% 0.21/0.51  % (3619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3619)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (3619)Memory used [KB]: 1791
% 0.21/0.51  % (3619)Time elapsed: 0.105 s
% 0.21/0.51  % (3619)------------------------------
% 0.21/0.51  % (3619)------------------------------
% 0.21/0.51  % (3597)Success in time 0.151 s
%------------------------------------------------------------------------------
