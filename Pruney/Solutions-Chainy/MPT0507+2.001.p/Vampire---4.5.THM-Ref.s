%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 138 expanded)
%              Number of leaves         :    4 (  27 expanded)
%              Depth                    :   17
%              Number of atoms          :  133 ( 437 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f171,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f170,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f170,plain,(
    ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f166,f11])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f166,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f151,f24])).

fof(f151,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f115,f121])).

fof(f121,plain,(
    r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2) ),
    inference(resolution,[],[f120,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(resolution,[],[f12,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f12,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f120,plain,(
    r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1) ),
    inference(subsumption_resolution,[],[f116,f14])).

fof(f116,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f91,f24])).

fof(f91,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1) ),
    inference(subsumption_resolution,[],[f80,f14])).

fof(f80,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1) ),
    inference(resolution,[],[f78,f26])).

fof(f26,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f78,plain,(
    r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f74,f14])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f56,f24])).

fof(f56,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f13,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,plain,(
    ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f115,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f114,f96])).

fof(f96,plain,(
    r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f92,f14])).

fof(f92,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f90,f24])).

fof(f90,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f79,f14])).

fof(f79,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0) ),
    inference(resolution,[],[f78,f27])).

fof(f27,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f114,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2) ),
    inference(subsumption_resolution,[],[f104,f11])).

fof(f104,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2) ),
    inference(resolution,[],[f57,f25])).

fof(f25,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f13,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:25:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (9075)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (9077)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (9083)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (9083)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f171,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) & r1_tarski(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f4])).
% 0.22/0.49  fof(f4,conjecture,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f170,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f166,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(resolution,[],[f151,f24])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.49    inference(resolution,[],[f115,f121])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2)),
% 0.22/0.49    inference(resolution,[],[f120,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f54,f14])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 0.22/0.49    inference(resolution,[],[f12,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    r1_tarski(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f116,f14])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f91,f24])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f80,f14])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK1)),
% 0.22/0.49    inference(resolution,[],[f78,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f74,f14])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f56,f24])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK1,sK0))),
% 0.22/0.49    inference(resolution,[],[f13,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f114,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f14])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f90,f24])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f79,f14])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0)),
% 0.22/0.49    inference(resolution,[],[f78,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0) | ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f104,f11])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~r2_hidden(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK0) | ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),sK2)),
% 0.22/0.49    inference(resolution,[],[f57,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X0) | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X0) | r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~r2_hidden(k4_tarski(sK3(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)),sK4(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.49    inference(resolution,[],[f13,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (9083)------------------------------
% 0.22/0.49  % (9083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9083)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (9083)Memory used [KB]: 1663
% 0.22/0.49  % (9083)Time elapsed: 0.074 s
% 0.22/0.49  % (9083)------------------------------
% 0.22/0.49  % (9083)------------------------------
% 0.22/0.49  % (9068)Success in time 0.129 s
%------------------------------------------------------------------------------
