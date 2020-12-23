%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:52 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   29 (  56 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 147 expanded)
%              Number of equality atoms :   14 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f41,f46,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f46,plain,(
    r2_hidden(sK5(sK1),k4_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f36,f39,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f39,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f16,f37])).

fof(f37,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f14,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f16,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    r2_hidden(sK5(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f35,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f35,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f17,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    r2_hidden(sK5(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f15,f36,f26])).

fof(f15,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:05:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.44  % (24428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.46  % (24428)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f70,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f41,f46,f32])).
% 0.18/0.46  fof(f32,plain,(
% 0.18/0.46    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.18/0.46    inference(equality_resolution,[],[f22])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.18/0.46    inference(cnf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.18/0.46  fof(f46,plain,(
% 0.18/0.46    r2_hidden(sK5(sK1),k4_xboole_0(sK0,sK2))),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f36,f39,f26])).
% 0.18/0.46  fof(f26,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f13])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.46  fof(f39,plain,(
% 0.18/0.46    r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.18/0.46    inference(backward_demodulation,[],[f16,f37])).
% 0.18/0.46  fof(f37,plain,(
% 0.18/0.46    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f14,f25])).
% 0.18/0.46  fof(f25,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f12])).
% 0.18/0.46  fof(f12,plain,(
% 0.18/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f6])).
% 0.18/0.46  fof(f6,axiom,(
% 0.18/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.18/0.46    inference(cnf_transformation,[],[f10])).
% 0.18/0.46  fof(f10,plain,(
% 0.18/0.46    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.18/0.46    inference(flattening,[],[f9])).
% 0.18/0.46  fof(f9,plain,(
% 0.18/0.46    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,negated_conjecture,(
% 0.18/0.46    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.18/0.46    inference(negated_conjecture,[],[f7])).
% 0.18/0.46  fof(f7,conjecture,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.18/0.46    inference(cnf_transformation,[],[f10])).
% 0.18/0.46  fof(f36,plain,(
% 0.18/0.46    r2_hidden(sK5(sK1),sK1)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f35,f29])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.46  fof(f35,plain,(
% 0.18/0.46    ~v1_xboole_0(sK1)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f17,f24])).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f11])).
% 0.18/0.46  fof(f11,plain,(
% 0.18/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    k1_xboole_0 != sK1),
% 0.18/0.46    inference(cnf_transformation,[],[f10])).
% 0.18/0.46  fof(f41,plain,(
% 0.18/0.46    r2_hidden(sK5(sK1),sK2)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f15,f36,f26])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    r1_tarski(sK1,sK2)),
% 0.18/0.46    inference(cnf_transformation,[],[f10])).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (24428)------------------------------
% 0.18/0.46  % (24428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (24428)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (24428)Memory used [KB]: 6268
% 0.18/0.46  % (24428)Time elapsed: 0.085 s
% 0.18/0.46  % (24428)------------------------------
% 0.18/0.46  % (24428)------------------------------
% 0.18/0.46  % (24423)Success in time 0.119 s
%------------------------------------------------------------------------------
