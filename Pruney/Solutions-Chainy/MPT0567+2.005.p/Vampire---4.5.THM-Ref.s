%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  25 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  52 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f152,f9])).

fof(f9,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f152,plain,(
    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f145,f10])).

fof(f10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f145,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k10_relat_1(sK0,k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f137,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f137,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK0,k1_xboole_0,X0),X0)
      | k10_relat_1(sK0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f80,f10])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k10_relat_1(sK0,X0) = X1
      | r2_hidden(sK1(sK0,X0,X1),X1) ) ),
    inference(resolution,[],[f24,f18])).

fof(f24,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(sK0,X5,X6),X5)
      | r2_hidden(sK1(sK0,X5,X6),X6)
      | k10_relat_1(sK0,X5) = X6 ) ),
    inference(resolution,[],[f8,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f8,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:52:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (9589)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (9593)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (9585)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (9583)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (9594)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (9594)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    inference(resolution,[],[f145,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_xboole_0(X1) | k10_relat_1(sK0,k1_xboole_0) = X1) )),
% 0.21/0.49    inference(resolution,[],[f137,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(sK0,k1_xboole_0,X0),X0) | k10_relat_1(sK0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(resolution,[],[f80,f10])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | k10_relat_1(sK0,X0) = X1 | r2_hidden(sK1(sK0,X0,X1),X1)) )),
% 0.21/0.49    inference(resolution,[],[f24,f18])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X6,X5] : (r2_hidden(sK3(sK0,X5,X6),X5) | r2_hidden(sK1(sK0,X5,X6),X6) | k10_relat_1(sK0,X5) = X6) )),
% 0.21/0.49    inference(resolution,[],[f8,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (9594)------------------------------
% 0.21/0.49  % (9594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9594)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (9594)Memory used [KB]: 1663
% 0.21/0.49  % (9594)Time elapsed: 0.083 s
% 0.21/0.49  % (9594)------------------------------
% 0.21/0.49  % (9594)------------------------------
% 0.21/0.49  % (9591)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (9580)Success in time 0.126 s
%------------------------------------------------------------------------------
