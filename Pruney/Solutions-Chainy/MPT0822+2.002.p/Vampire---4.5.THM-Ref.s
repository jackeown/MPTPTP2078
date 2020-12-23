%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 174 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 453 expanded)
%              Number of equality atoms :   25 ( 122 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(subsumption_resolution,[],[f82,f62])).

fof(f62,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f42,plain,
    ( sK1 != k2_relat_1(sK2)
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f16,f40])).

fof(f40,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f19,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f16,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ r2_hidden(sK3,sK1) ),
    inference(inner_rewriting,[],[f60])).

fof(f60,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(resolution,[],[f43,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f43,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | sK1 != k2_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f17,f40])).

fof(f17,plain,(
    ! [X4] :
      ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f79,f52])).

fof(f52,plain,
    ( r2_xboole_0(k2_relat_1(sK2),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f50,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f50,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f49,f41])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f19,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f49,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f39,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f39,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f19,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f79,plain,(
    ~ r2_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f75,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f75,plain,(
    r2_hidden(sK8(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    r2_hidden(k4_tarski(sK4(sK8(k2_relat_1(sK2),sK1)),sK8(k2_relat_1(sK2),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f73,f62])).

fof(f73,plain,
    ( r2_hidden(k4_tarski(sK4(sK8(k2_relat_1(sK2),sK1)),sK8(k2_relat_1(sK2),sK1)),sK2)
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f71,f52])).

fof(f71,plain,(
    ! [X3] :
      ( ~ r2_xboole_0(X3,sK1)
      | r2_hidden(k4_tarski(sK4(sK8(X3,sK1)),sK8(X3,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f68,f62])).

fof(f68,plain,(
    ! [X3] :
      ( sK1 = k2_relat_1(sK2)
      | r2_hidden(k4_tarski(sK4(sK8(X3,sK1)),sK8(X3,sK1)),sK2)
      | ~ r2_xboole_0(X3,sK1) ) ),
    inference(resolution,[],[f44,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | sK1 = k2_relat_1(sK2)
      | r2_hidden(k4_tarski(sK4(X3),X3),sK2) ) ),
    inference(backward_demodulation,[],[f18,f40])).

fof(f18,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(sK4(X3),X3),sK2) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (16587)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (16587)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (16573)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (16579)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f82,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    sK1 != k2_relat_1(sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f61,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    sK1 != k2_relat_1(sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.47    inference(backward_demodulation,[],[f16,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.47    inference(resolution,[],[f19,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    sK1 != k2_relat_1(sK2) | ~r2_hidden(sK3,sK1)),
% 0.21/0.47    inference(inner_rewriting,[],[f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    sK1 != k2_relat_1(sK2) | ~r2_hidden(sK3,k2_relat_1(sK2))),
% 0.21/0.47    inference(resolution,[],[f43,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.47    inference(equality_resolution,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | sK1 != k2_relat_1(sK2)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f17,f40])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X4] : (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    sK1 = k2_relat_1(sK2)),
% 0.21/0.47    inference(resolution,[],[f79,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    r2_xboole_0(k2_relat_1(sK2),sK1) | sK1 = k2_relat_1(sK2)),
% 0.21/0.47    inference(resolution,[],[f50,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f49,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(resolution,[],[f19,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.47    inference(resolution,[],[f39,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    v5_relat_1(sK2,sK1)),
% 0.21/0.47    inference(resolution,[],[f19,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ~r2_xboole_0(k2_relat_1(sK2),sK1)),
% 0.21/0.47    inference(resolution,[],[f75,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK8(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    r2_hidden(sK8(k2_relat_1(sK2),sK1),k2_relat_1(sK2))),
% 0.21/0.47    inference(resolution,[],[f74,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4(sK8(k2_relat_1(sK2),sK1)),sK8(k2_relat_1(sK2),sK1)),sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f73,f62])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4(sK8(k2_relat_1(sK2),sK1)),sK8(k2_relat_1(sK2),sK1)),sK2) | sK1 = k2_relat_1(sK2)),
% 0.21/0.47    inference(resolution,[],[f71,f52])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X3] : (~r2_xboole_0(X3,sK1) | r2_hidden(k4_tarski(sK4(sK8(X3,sK1)),sK8(X3,sK1)),sK2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f68,f62])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X3] : (sK1 = k2_relat_1(sK2) | r2_hidden(k4_tarski(sK4(sK8(X3,sK1)),sK8(X3,sK1)),sK2) | ~r2_xboole_0(X3,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f44,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK8(X0,X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X3] : (~r2_hidden(X3,sK1) | sK1 = k2_relat_1(sK2) | r2_hidden(k4_tarski(sK4(X3),X3),sK2)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f18,f40])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(sK4(X3),X3),sK2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16587)------------------------------
% 0.21/0.47  % (16587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16587)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16587)Memory used [KB]: 1663
% 0.21/0.47  % (16587)Time elapsed: 0.064 s
% 0.21/0.47  % (16587)------------------------------
% 0.21/0.47  % (16587)------------------------------
% 0.21/0.48  % (16570)Success in time 0.117 s
%------------------------------------------------------------------------------
