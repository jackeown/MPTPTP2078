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
% DateTime   : Thu Dec  3 12:55:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 128 expanded)
%              Number of leaves         :    3 (  23 expanded)
%              Depth                    :   18
%              Number of atoms          :  135 ( 665 expanded)
%              Number of equality atoms :   16 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f25])).

fof(f25,plain,(
    r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f24,f14])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ( r2_hidden(X3,X1)
                         => r2_hidden(k4_tarski(X2,X3),X0) )
                      & r2_hidden(X2,X1) )
                & k1_xboole_0 != X1
                & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

fof(f24,plain,
    ( ~ v1_relat_1(sK0)
    | r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0)
      | r2_wellord1(X0,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

fof(f15,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ~ r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f73,f12])).

fof(f12,plain,(
    r1_tarski(sK1,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ r2_wellord1(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f72,f25])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
      | ~ r2_wellord1(sK0,X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f54,f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,X0)
      | ~ r2_wellord1(sK0,X0)
      | ~ r2_wellord1(sK0,X1)
      | ~ r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f53,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,X0)
      | ~ r2_wellord1(sK0,X0)
      | ~ r2_wellord1(sK0,X1)
      | ~ r1_tarski(sK1,X1)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f52,f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,X0)
      | ~ r2_wellord1(sK0,X0)
      | ~ v1_relat_1(sK0)
      | ~ r2_wellord1(sK0,X1)
      | ~ r1_tarski(sK1,X1)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f43,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_wellord1(X1,X0)
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X2
      | r2_hidden(sK3(X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).

fof(f43,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,sK1),sK1)
      | ~ r1_tarski(sK1,X0)
      | ~ r2_wellord1(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f40,f13])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r2_wellord1(sK0,X0)
      | ~ r1_tarski(sK1,X0)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(sK3(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(sK3(sK0,X0)),X0)
      | ~ r2_wellord1(sK0,X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK3(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f34,f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(sK0,X0),sK1)
      | ~ v1_relat_1(sK0)
      | ~ r2_wellord1(sK0,X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK2(sK3(sK0,X0)),X0) ) ),
    inference(resolution,[],[f11,f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_wellord1(X1,X0)
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X2
      | ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(sK3(X1,X2),X4),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    r2_hidden(sK2(sK3(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f38,f14])).

fof(f38,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK2(sK3(sK0,sK1)),sK1) ),
    inference(resolution,[],[f36,f25])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_wellord1(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(sK3(X0,sK1)),sK1) ) ),
    inference(resolution,[],[f33,f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,X1)
      | ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r2_hidden(sK2(sK3(X0,sK1)),sK1) ) ),
    inference(subsumption_resolution,[],[f31,f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK3(X0,sK1)),sK1)
      | ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | ~ r1_tarski(sK1,X1)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f10,f19])).

fof(f10,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(sK2(X2),sK1) ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (17478)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (17483)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (17483)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f74,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f24,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0))) & v2_wellord1(X0) & v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f5])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0] : ((? [X1] : (! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0))) & v2_wellord1(X0)) & v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f3])).
% 0.20/0.47  fof(f3,conjecture,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ~v1_relat_1(sK0) | r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(resolution,[],[f15,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v2_wellord1(X0) | r2_wellord1(X0,k3_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0] : ((r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    v2_wellord1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ~r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(resolution,[],[f73,f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    r1_tarski(sK1,k3_relat_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r2_wellord1(sK0,X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f72,f25])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_wellord1(sK0,k3_relat_1(sK0)) | ~r2_wellord1(sK0,X0) | ~r1_tarski(sK1,X0)) )),
% 0.20/0.47    inference(resolution,[],[f54,f12])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | ~r2_wellord1(sK0,X0) | ~r2_wellord1(sK0,X1) | ~r1_tarski(sK1,X1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f53,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    k1_xboole_0 != sK1),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | ~r2_wellord1(sK0,X0) | ~r2_wellord1(sK0,X1) | ~r1_tarski(sK1,X1) | k1_xboole_0 = sK1) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f52,f14])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | ~r2_wellord1(sK0,X0) | ~v1_relat_1(sK0) | ~r2_wellord1(sK0,X1) | ~r1_tarski(sK1,X1) | k1_xboole_0 = sK1) )),
% 0.20/0.47    inference(resolution,[],[f43,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r2_wellord1(X1,X0) | ~r1_tarski(X2,X0) | k1_xboole_0 = X2 | r2_hidden(sK3(X1,X2),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : ((! [X2] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_wellord1(X1,X0) => ! [X2] : ~(! [X3] : ~(! [X4] : (r2_hidden(X4,X2) => r2_hidden(k4_tarski(X3,X4),X1)) & r2_hidden(X3,X2)) & k1_xboole_0 != X2 & r1_tarski(X2,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK3(sK0,sK1),sK1) | ~r1_tarski(sK1,X0) | ~r2_wellord1(sK0,X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f40,f13])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_wellord1(sK0,X0) | ~r1_tarski(sK1,X0) | k1_xboole_0 = sK1 | ~r2_hidden(sK3(sK0,sK1),sK1)) )),
% 0.20/0.47    inference(resolution,[],[f39,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK2(sK3(sK0,X0)),X0) | ~r2_wellord1(sK0,X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0 | ~r2_hidden(sK3(sK0,X0),sK1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f34,f14])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,X0),sK1) | ~v1_relat_1(sK0) | ~r2_wellord1(sK0,X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0 | ~r2_hidden(sK2(sK3(sK0,X0)),X0)) )),
% 0.20/0.48    inference(resolution,[],[f11,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X1) | ~r2_wellord1(X1,X0) | ~r1_tarski(X2,X0) | k1_xboole_0 = X2 | ~r2_hidden(X4,X2) | r2_hidden(k4_tarski(sK3(X1,X2),X4),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(k4_tarski(X2,sK2(X2)),sK0) | ~r2_hidden(X2,sK1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    r2_hidden(sK2(sK3(sK0,sK1)),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f38,f14])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~v1_relat_1(sK0) | r2_hidden(sK2(sK3(sK0,sK1)),sK1)),
% 0.20/0.48    inference(resolution,[],[f36,f25])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_wellord1(X0,k3_relat_1(sK0)) | ~v1_relat_1(X0) | r2_hidden(sK2(sK3(X0,sK1)),sK1)) )),
% 0.20/0.48    inference(resolution,[],[f33,f12])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(sK1,X1) | ~v1_relat_1(X0) | ~r2_wellord1(X0,X1) | r2_hidden(sK2(sK3(X0,sK1)),sK1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f31,f13])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(sK3(X0,sK1)),sK1) | ~v1_relat_1(X0) | ~r2_wellord1(X0,X1) | ~r1_tarski(sK1,X1) | k1_xboole_0 = sK1) )),
% 0.20/0.48    inference(resolution,[],[f10,f19])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(sK2(X2),sK1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17483)------------------------------
% 0.20/0.48  % (17483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17483)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17483)Memory used [KB]: 1663
% 0.20/0.48  % (17483)Time elapsed: 0.009 s
% 0.20/0.48  % (17483)------------------------------
% 0.20/0.48  % (17483)------------------------------
% 0.20/0.48  % (17469)Success in time 0.118 s
%------------------------------------------------------------------------------
