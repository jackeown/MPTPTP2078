%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  70 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :   21
%              Number of atoms          :  107 ( 212 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f11])).

fof(f11,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f5])).

% (31979)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f110,plain,(
    r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f108,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f107,f11])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,sK2)
      | r1_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f85,f15])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK1,X1),sK2)
      | r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f83,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f83,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(sK1,X2),sK2)
      | r2_hidden(k4_tarski(sK3(sK0),sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(sK1,X2)
      | r1_tarski(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f81,f10])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(sK1,X2),sK2)
      | r1_tarski(sK1,X2)
      | r2_hidden(k4_tarski(sK3(sK0),sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(sK1,X3)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f59,f12])).

fof(f12,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f59,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | r2_hidden(sK4(sK1,X4),sK2)
      | r1_tarski(sK1,X4)
      | r2_hidden(k4_tarski(X2,sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(sK1,X3) ) ),
    inference(resolution,[],[f51,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f49,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | r1_tarski(sK1,X0)
      | r2_hidden(X1,k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X0),sK2) ) ),
    inference(resolution,[],[f48,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f46,f10])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f31,f12])).

fof(f31,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X2),sK2)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f29,f14])).

fof(f29,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X2,sK0)
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f25,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK0))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f22,f18])).

fof(f22,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK0))
      | r2_hidden(X0,k2_zfmisc_1(sK2,sK0))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ) ),
    inference(resolution,[],[f9,f13])).

fof(f9,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (31964)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (31956)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (31956)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f110,f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  % (31979)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  fof(f5,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.20/0.51    inference(negated_conjecture,[],[f4])).
% 0.20/0.51  fof(f4,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    r1_tarski(sK1,sK2)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f109])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.20/0.51    inference(resolution,[],[f108,f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f107,f11])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0) | r1_tarski(sK1,sK2)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0) | r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2)) )),
% 0.20/0.51    inference(resolution,[],[f85,f15])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK4(sK1,X1),sK2) | r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0) | r1_tarski(sK1,X1)) )),
% 0.20/0.51    inference(resolution,[],[f83,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X2,X3] : (r2_hidden(sK4(sK1,X2),sK2) | r2_hidden(k4_tarski(sK3(sK0),sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2)) | r1_tarski(sK1,X2) | r1_tarski(sK1,X3)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f81,f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    k1_xboole_0 != sK0),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X2,X3] : (r2_hidden(sK4(sK1,X2),sK2) | r1_tarski(sK1,X2) | r2_hidden(k4_tarski(sK3(sK0),sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2)) | r1_tarski(sK1,X3) | k1_xboole_0 = sK0) )),
% 0.20/0.51    inference(resolution,[],[f59,f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (~r2_hidden(X2,sK0) | r2_hidden(sK4(sK1,X4),sK2) | r1_tarski(sK1,X4) | r2_hidden(k4_tarski(X2,sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2)) | r1_tarski(sK1,X3)) )),
% 0.20/0.51    inference(resolution,[],[f51,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,sK1) | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(sK0,sK2)) | r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0) | ~r2_hidden(X1,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f49,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK1,X0) | r2_hidden(X1,k2_zfmisc_1(sK0,sK2)) | r2_hidden(sK4(sK1,X0),sK2)) )),
% 0.20/0.51    inference(resolution,[],[f48,f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f46,f10])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0) | k1_xboole_0 = sK0) )),
% 0.20/0.51    inference(resolution,[],[f31,f12])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_hidden(X1,sK0) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r2_hidden(sK4(sK1,X2),sK2) | r1_tarski(sK1,X2)) )),
% 0.20/0.51    inference(resolution,[],[f29,f14])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(X2,sK0) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r2_hidden(X3,sK2)) )),
% 0.20/0.51    inference(resolution,[],[f25,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK0)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.51    inference(resolution,[],[f22,f18])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) | r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))) )),
% 0.20/0.51    inference(resolution,[],[f9,f13])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (31956)------------------------------
% 0.20/0.51  % (31956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31956)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (31956)Memory used [KB]: 6268
% 0.20/0.51  % (31956)Time elapsed: 0.071 s
% 0.20/0.51  % (31956)------------------------------
% 0.20/0.51  % (31956)------------------------------
% 0.20/0.51  % (31949)Success in time 0.151 s
%------------------------------------------------------------------------------
