%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:38 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   42 (  96 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 260 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f133,f108])).

fof(f108,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(subsumption_resolution,[],[f105,f70])).

fof(f70,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f67,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f67,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f59,f43])).

fof(f43,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f20,f26])).

fof(f20,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f59,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f52,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f21,f26])).

fof(f21,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f105,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f32,f87])).

fof(f87,plain,(
    k3_xboole_0(sK0,sK1) = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f84,f78])).

fof(f78,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f70,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f84,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | k3_xboole_0(sK0,sK1) = k1_tarski(sK3) ),
    inference(resolution,[],[f18,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f18,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f133,plain,(
    r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(resolution,[],[f92,f43])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | r1_xboole_0(k1_tarski(sK3),X0) ) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f19,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f19,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.38  ipcrm: permission denied for id (814415886)
% 0.14/0.38  ipcrm: permission denied for id (814448656)
% 0.21/0.41  ipcrm: permission denied for id (814546979)
% 0.21/0.41  ipcrm: permission denied for id (814579748)
% 0.21/0.42  ipcrm: permission denied for id (814743598)
% 0.21/0.45  ipcrm: permission denied for id (814874693)
% 0.21/0.46  ipcrm: permission denied for id (814940240)
% 0.21/0.47  ipcrm: permission denied for id (815038550)
% 0.21/0.47  ipcrm: permission denied for id (815104092)
% 0.21/0.47  ipcrm: permission denied for id (815136861)
% 0.21/0.48  ipcrm: permission denied for id (815202401)
% 0.21/0.48  ipcrm: permission denied for id (815235172)
% 0.21/0.49  ipcrm: permission denied for id (815300713)
% 0.21/0.51  ipcrm: permission denied for id (815431802)
% 0.37/0.63  % (10629)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.37/0.63  % (10632)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.37/0.63  % (10631)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.37/0.63  % (10637)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.37/0.64  % (10638)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.37/0.64  % (10625)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.37/0.64  % (10640)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.37/0.64  % (10630)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.37/0.64  % (10644)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.37/0.64  % (10637)Refutation found. Thanks to Tanya!
% 0.37/0.64  % SZS status Theorem for theBenchmark
% 0.37/0.64  % SZS output start Proof for theBenchmark
% 0.37/0.64  fof(f142,plain,(
% 0.37/0.64    $false),
% 0.37/0.64    inference(subsumption_resolution,[],[f133,f108])).
% 0.37/0.64  fof(f108,plain,(
% 0.37/0.64    ~r1_xboole_0(k1_tarski(sK3),sK1)),
% 0.37/0.64    inference(subsumption_resolution,[],[f105,f70])).
% 0.37/0.64  fof(f70,plain,(
% 0.37/0.64    ~r1_xboole_0(sK0,sK1)),
% 0.37/0.64    inference(resolution,[],[f67,f26])).
% 0.37/0.64  fof(f26,plain,(
% 0.37/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f15])).
% 0.37/0.64  fof(f15,plain,(
% 0.37/0.64    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.37/0.64    inference(ennf_transformation,[],[f2])).
% 0.37/0.64  fof(f2,axiom,(
% 0.37/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.37/0.64  fof(f67,plain,(
% 0.37/0.64    ~r1_xboole_0(sK1,sK0)),
% 0.37/0.64    inference(subsumption_resolution,[],[f59,f43])).
% 0.37/0.64  fof(f43,plain,(
% 0.37/0.64    r1_xboole_0(sK1,sK2)),
% 0.37/0.64    inference(resolution,[],[f20,f26])).
% 0.37/0.64  fof(f20,plain,(
% 0.37/0.64    r1_xboole_0(sK2,sK1)),
% 0.37/0.64    inference(cnf_transformation,[],[f12])).
% 0.37/0.64  fof(f12,plain,(
% 0.37/0.64    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.37/0.64    inference(flattening,[],[f11])).
% 0.37/0.64  fof(f11,plain,(
% 0.37/0.64    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.37/0.64    inference(ennf_transformation,[],[f9])).
% 0.37/0.64  fof(f9,negated_conjecture,(
% 0.37/0.64    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.37/0.64    inference(negated_conjecture,[],[f8])).
% 0.37/0.64  fof(f8,conjecture,(
% 0.37/0.64    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.37/0.64  fof(f59,plain,(
% 0.37/0.64    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 0.37/0.64    inference(resolution,[],[f52,f35])).
% 0.37/0.64  fof(f35,plain,(
% 0.37/0.64    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f17])).
% 0.37/0.64  fof(f17,plain,(
% 0.37/0.64    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.37/0.64    inference(ennf_transformation,[],[f4])).
% 0.37/0.64  fof(f4,axiom,(
% 0.37/0.64    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.37/0.64  fof(f52,plain,(
% 0.37/0.64    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.37/0.64    inference(resolution,[],[f21,f26])).
% 0.37/0.64  fof(f21,plain,(
% 0.37/0.64    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.37/0.64    inference(cnf_transformation,[],[f12])).
% 0.37/0.64  fof(f105,plain,(
% 0.37/0.64    ~r1_xboole_0(k1_tarski(sK3),sK1) | r1_xboole_0(sK0,sK1)),
% 0.37/0.64    inference(superposition,[],[f32,f87])).
% 0.37/0.64  fof(f87,plain,(
% 0.37/0.64    k3_xboole_0(sK0,sK1) = k1_tarski(sK3)),
% 0.37/0.64    inference(subsumption_resolution,[],[f84,f78])).
% 0.37/0.64  fof(f78,plain,(
% 0.37/0.64    k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 0.37/0.64    inference(resolution,[],[f70,f27])).
% 0.37/0.64  fof(f27,plain,(
% 0.37/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f1])).
% 0.37/0.64  fof(f1,axiom,(
% 0.37/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.37/0.64  fof(f84,plain,(
% 0.37/0.64    k1_xboole_0 = k3_xboole_0(sK0,sK1) | k3_xboole_0(sK0,sK1) = k1_tarski(sK3)),
% 0.37/0.64    inference(resolution,[],[f18,f29])).
% 0.37/0.64  fof(f29,plain,(
% 0.37/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.37/0.64    inference(cnf_transformation,[],[f7])).
% 0.37/0.64  fof(f7,axiom,(
% 0.37/0.64    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.37/0.64  fof(f18,plain,(
% 0.37/0.64    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.37/0.64    inference(cnf_transformation,[],[f12])).
% 0.37/0.64  fof(f32,plain,(
% 0.37/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f16])).
% 0.37/0.64  fof(f16,plain,(
% 0.37/0.64    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.37/0.64    inference(ennf_transformation,[],[f5])).
% 0.37/0.64  fof(f5,axiom,(
% 0.37/0.64    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.37/0.64  fof(f133,plain,(
% 0.37/0.64    r1_xboole_0(k1_tarski(sK3),sK1)),
% 0.37/0.64    inference(resolution,[],[f92,f43])).
% 0.37/0.64  fof(f92,plain,(
% 0.37/0.64    ( ! [X0] : (~r1_xboole_0(X0,sK2) | r1_xboole_0(k1_tarski(sK3),X0)) )),
% 0.37/0.64    inference(resolution,[],[f38,f25])).
% 0.37/0.64  fof(f25,plain,(
% 0.37/0.64    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f14])).
% 0.37/0.64  fof(f14,plain,(
% 0.37/0.64    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.37/0.64    inference(ennf_transformation,[],[f6])).
% 0.37/0.64  fof(f6,axiom,(
% 0.37/0.64    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.37/0.64  fof(f38,plain,(
% 0.37/0.64    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.37/0.64    inference(resolution,[],[f19,f22])).
% 0.37/0.64  fof(f22,plain,(
% 0.37/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f13])).
% 0.37/0.64  fof(f13,plain,(
% 0.37/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.37/0.64    inference(ennf_transformation,[],[f10])).
% 0.37/0.64  fof(f10,plain,(
% 0.37/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.37/0.64    inference(rectify,[],[f3])).
% 0.37/0.64  fof(f3,axiom,(
% 0.37/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.37/0.64  fof(f19,plain,(
% 0.37/0.64    r2_hidden(sK3,sK2)),
% 0.37/0.64    inference(cnf_transformation,[],[f12])).
% 0.37/0.64  % SZS output end Proof for theBenchmark
% 0.37/0.64  % (10637)------------------------------
% 0.37/0.64  % (10637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.64  % (10637)Termination reason: Refutation
% 0.37/0.64  
% 0.37/0.64  % (10637)Memory used [KB]: 1663
% 0.37/0.64  % (10637)Time elapsed: 0.081 s
% 0.37/0.64  % (10637)------------------------------
% 0.37/0.64  % (10637)------------------------------
% 0.37/0.64  % (10490)Success in time 0.287 s
%------------------------------------------------------------------------------
