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
% DateTime   : Thu Dec  3 12:55:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :   81 ( 109 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f18])).

fof(f18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f36,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f35,plain,(
    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f34,f20])).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f34,plain,(
    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f33,f15])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f33,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f32,f28])).

fof(f28,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f23,f19])).

fof(f19,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f23,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f32,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f31,f29])).

fof(f29,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f22,f19])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f30,f16])).

fof(f16,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f25,f17])).

fof(f17,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:11:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.40  % (15950)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.40  % (15945)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.40  % (15945)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f37,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(subsumption_resolution,[],[f36,f18])).
% 0.20/0.40  fof(f18,plain,(
% 0.20/0.40    v1_xboole_0(k1_xboole_0)),
% 0.20/0.40    inference(cnf_transformation,[],[f2])).
% 0.20/0.40  fof(f2,axiom,(
% 0.20/0.40    v1_xboole_0(k1_xboole_0)),
% 0.20/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.40  fof(f36,plain,(
% 0.20/0.40    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.40    inference(resolution,[],[f35,f27])).
% 0.20/0.40  fof(f27,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f14])).
% 0.20/0.40  fof(f14,plain,(
% 0.20/0.40    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.40    inference(ennf_transformation,[],[f9])).
% 0.20/0.40  fof(f9,plain,(
% 0.20/0.40    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.40    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.40  fof(f1,axiom,(
% 0.20/0.40    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.40  fof(f35,plain,(
% 0.20/0.40    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.40    inference(forward_demodulation,[],[f34,f20])).
% 0.20/0.40  fof(f20,plain,(
% 0.20/0.40    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.40    inference(cnf_transformation,[],[f3])).
% 0.20/0.40  fof(f3,axiom,(
% 0.20/0.40    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.40  fof(f34,plain,(
% 0.20/0.40    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.20/0.40    inference(subsumption_resolution,[],[f33,f15])).
% 0.20/0.40  fof(f15,plain,(
% 0.20/0.40    v1_relat_1(sK0)),
% 0.20/0.40    inference(cnf_transformation,[],[f11])).
% 0.20/0.40  fof(f11,plain,(
% 0.20/0.40    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.40    inference(flattening,[],[f10])).
% 0.20/0.40  fof(f10,plain,(
% 0.20/0.40    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.40    inference(ennf_transformation,[],[f8])).
% 0.20/0.40  fof(f8,negated_conjecture,(
% 0.20/0.40    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.20/0.40    inference(negated_conjecture,[],[f7])).
% 0.20/0.40  fof(f7,conjecture,(
% 0.20/0.40    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.20/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.20/0.40  fof(f33,plain,(
% 0.20/0.40    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 0.20/0.40    inference(subsumption_resolution,[],[f32,f28])).
% 0.20/0.40  fof(f28,plain,(
% 0.20/0.40    v1_funct_1(k1_xboole_0)),
% 0.20/0.40    inference(superposition,[],[f23,f19])).
% 0.20/0.40  fof(f19,plain,(
% 0.20/0.40    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.40    inference(cnf_transformation,[],[f4])).
% 0.20/0.40  fof(f4,axiom,(
% 0.20/0.40    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.40  fof(f23,plain,(
% 0.20/0.40    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.40    inference(cnf_transformation,[],[f6])).
% 0.20/0.40  fof(f6,axiom,(
% 0.20/0.40    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.40  fof(f32,plain,(
% 0.20/0.40    ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 0.20/0.40    inference(subsumption_resolution,[],[f31,f29])).
% 0.20/0.40  fof(f29,plain,(
% 0.20/0.40    v1_relat_1(k1_xboole_0)),
% 0.20/0.40    inference(superposition,[],[f22,f19])).
% 0.20/0.40  fof(f22,plain,(
% 0.20/0.40    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.40    inference(cnf_transformation,[],[f6])).
% 0.20/0.40  fof(f31,plain,(
% 0.20/0.40    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 0.20/0.40    inference(subsumption_resolution,[],[f30,f16])).
% 0.20/0.40  fof(f16,plain,(
% 0.20/0.40    v1_funct_1(sK0)),
% 0.20/0.40    inference(cnf_transformation,[],[f11])).
% 0.20/0.40  fof(f30,plain,(
% 0.20/0.40    ~v1_funct_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 0.20/0.40    inference(resolution,[],[f25,f17])).
% 0.20/0.40  fof(f17,plain,(
% 0.20/0.40    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.20/0.40    inference(cnf_transformation,[],[f11])).
% 0.20/0.40  fof(f25,plain,(
% 0.20/0.40    ( ! [X0,X1] : (v5_funct_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f13])).
% 0.20/0.40  fof(f13,plain,(
% 0.20/0.40    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.40    inference(flattening,[],[f12])).
% 0.20/0.40  fof(f12,plain,(
% 0.20/0.40    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.40    inference(ennf_transformation,[],[f5])).
% 0.20/0.40  fof(f5,axiom,(
% 0.20/0.40    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.20/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.20/0.40  % SZS output end Proof for theBenchmark
% 0.20/0.40  % (15945)------------------------------
% 0.20/0.40  % (15945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.40  % (15945)Termination reason: Refutation
% 0.20/0.40  
% 0.20/0.40  % (15945)Memory used [KB]: 10490
% 0.20/0.40  % (15945)Time elapsed: 0.003 s
% 0.20/0.40  % (15945)------------------------------
% 0.20/0.40  % (15945)------------------------------
% 0.20/0.40  % (15952)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.40  % (15944)Success in time 0.062 s
%------------------------------------------------------------------------------
