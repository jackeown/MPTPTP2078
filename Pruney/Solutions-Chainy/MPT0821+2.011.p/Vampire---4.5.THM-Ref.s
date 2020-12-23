%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 194 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :   97 ( 503 expanded)
%              Number of equality atoms :   32 ( 161 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(subsumption_resolution,[],[f418,f73])).

fof(f73,plain,(
    sK1 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f72,f40])).

fof(f40,plain,
    ( sK1 != k1_relat_1(sK2)
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f12,f38])).

fof(f38,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f15,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f12,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,
    ( sK1 != k1_relat_1(sK2)
    | ~ r2_hidden(sK3,sK1) ),
    inference(inner_rewriting,[],[f67])).

fof(f67,plain,
    ( sK1 != k1_relat_1(sK2)
    | ~ r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f41,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | sK1 != k1_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f13,f38])).

fof(f13,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f418,plain,(
    sK1 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f411,f403])).

fof(f403,plain,(
    r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f400,f73])).

fof(f400,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | sK1 = k1_relat_1(sK2) ),
    inference(factoring,[],[f375])).

fof(f375,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),X0)
      | r2_hidden(sK5(sK2,X0),sK1)
      | k1_relat_1(sK2) = X0 ) ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f60,plain,(
    ! [X10] :
      ( r2_hidden(k4_tarski(sK5(sK2,X10),sK7(sK2,X10)),k2_zfmisc_1(sK1,sK0))
      | r2_hidden(sK5(sK2,X10),X10)
      | k1_relat_1(sK2) = X10 ) ),
    inference(resolution,[],[f54,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,k2_zfmisc_1(sK1,sK0)) ) ),
    inference(superposition,[],[f36,f46])).

fof(f46,plain,(
    sK2 = k3_xboole_0(sK2,k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f39,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f39,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f15,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

% (25453)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (25450)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f411,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | sK1 = k1_relat_1(sK2) ),
    inference(resolution,[],[f410,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f410,plain,(
    r2_hidden(k4_tarski(sK5(sK2,sK1),sK4(sK5(sK2,sK1))),sK2) ),
    inference(subsumption_resolution,[],[f405,f73])).

fof(f405,plain,
    ( sK1 = k1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK5(sK2,sK1),sK4(sK5(sK2,sK1))),sK2) ),
    inference(resolution,[],[f403,f42])).

fof(f42,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | sK1 = k1_relat_1(sK2)
      | r2_hidden(k4_tarski(X3,sK4(X3)),sK2) ) ),
    inference(backward_demodulation,[],[f14,f38])).

fof(f14,plain,(
    ! [X3] :
      ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(X3,sK4(X3)),sK2) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:58:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.50  % (25454)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.50  % (25461)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.50  % (25460)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.50  % (25452)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.50  % (25451)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (25463)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.23/0.52  % (25460)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f419,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(subsumption_resolution,[],[f418,f73])).
% 0.23/0.52  fof(f73,plain,(
% 0.23/0.52    sK1 != k1_relat_1(sK2)),
% 0.23/0.52    inference(subsumption_resolution,[],[f72,f40])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    sK1 != k1_relat_1(sK2) | r2_hidden(sK3,sK1)),
% 0.23/0.52    inference(backward_demodulation,[],[f12,f38])).
% 0.23/0.52  fof(f38,plain,(
% 0.23/0.52    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.23/0.52    inference(resolution,[],[f15,f23])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f11])).
% 0.23/0.52  fof(f11,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.52    inference(cnf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,plain,(
% 0.23/0.52    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.23/0.52    inference(ennf_transformation,[],[f8])).
% 0.23/0.52  fof(f8,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.23/0.52    inference(negated_conjecture,[],[f7])).
% 0.23/0.52  fof(f7,conjecture,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    sK1 != k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f9])).
% 0.23/0.52  fof(f72,plain,(
% 0.23/0.52    sK1 != k1_relat_1(sK2) | ~r2_hidden(sK3,sK1)),
% 0.23/0.52    inference(inner_rewriting,[],[f67])).
% 0.23/0.52  fof(f67,plain,(
% 0.23/0.52    sK1 != k1_relat_1(sK2) | ~r2_hidden(sK3,k1_relat_1(sK2))),
% 0.23/0.52    inference(resolution,[],[f41,f33])).
% 0.23/0.52  fof(f33,plain,(
% 0.23/0.52    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.23/0.52    inference(equality_resolution,[],[f18])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.23/0.52  fof(f41,plain,(
% 0.23/0.52    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | sK1 != k1_relat_1(sK2)) )),
% 0.23/0.52    inference(backward_demodulation,[],[f13,f38])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ( ! [X4] : (sK1 != k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f9])).
% 0.23/0.52  fof(f418,plain,(
% 0.23/0.52    sK1 = k1_relat_1(sK2)),
% 0.23/0.52    inference(subsumption_resolution,[],[f411,f403])).
% 0.23/0.52  fof(f403,plain,(
% 0.23/0.52    r2_hidden(sK5(sK2,sK1),sK1)),
% 0.23/0.52    inference(subsumption_resolution,[],[f400,f73])).
% 0.23/0.52  fof(f400,plain,(
% 0.23/0.52    r2_hidden(sK5(sK2,sK1),sK1) | sK1 = k1_relat_1(sK2)),
% 0.23/0.52    inference(factoring,[],[f375])).
% 0.23/0.52  fof(f375,plain,(
% 0.23/0.52    ( ! [X0] : (r2_hidden(sK5(sK2,X0),X0) | r2_hidden(sK5(sK2,X0),sK1) | k1_relat_1(sK2) = X0) )),
% 0.23/0.52    inference(resolution,[],[f60,f30])).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.23/0.52  fof(f60,plain,(
% 0.23/0.52    ( ! [X10] : (r2_hidden(k4_tarski(sK5(sK2,X10),sK7(sK2,X10)),k2_zfmisc_1(sK1,sK0)) | r2_hidden(sK5(sK2,X10),X10) | k1_relat_1(sK2) = X10) )),
% 0.23/0.52    inference(resolution,[],[f54,f19])).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f5])).
% 0.23/0.52  fof(f54,plain,(
% 0.23/0.52    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(X4,k2_zfmisc_1(sK1,sK0))) )),
% 0.23/0.52    inference(superposition,[],[f36,f46])).
% 0.23/0.52  fof(f46,plain,(
% 0.23/0.52    sK2 = k3_xboole_0(sK2,k2_zfmisc_1(sK1,sK0))),
% 0.23/0.52    inference(resolution,[],[f39,f16])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.52    inference(cnf_transformation,[],[f10])).
% 0.23/0.52  fof(f10,plain,(
% 0.23/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    r1_tarski(sK2,k2_zfmisc_1(sK1,sK0))),
% 0.23/0.52    inference(resolution,[],[f15,f22])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.53  % (25453)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.53  % (25450)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.23/0.54    inference(equality_resolution,[],[f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.23/0.54    inference(cnf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.23/0.54  fof(f411,plain,(
% 0.23/0.54    ~r2_hidden(sK5(sK2,sK1),sK1) | sK1 = k1_relat_1(sK2)),
% 0.23/0.54    inference(resolution,[],[f410,f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f5])).
% 0.23/0.54  fof(f410,plain,(
% 0.23/0.54    r2_hidden(k4_tarski(sK5(sK2,sK1),sK4(sK5(sK2,sK1))),sK2)),
% 0.23/0.54    inference(subsumption_resolution,[],[f405,f73])).
% 0.23/0.54  fof(f405,plain,(
% 0.23/0.54    sK1 = k1_relat_1(sK2) | r2_hidden(k4_tarski(sK5(sK2,sK1),sK4(sK5(sK2,sK1))),sK2)),
% 0.23/0.54    inference(resolution,[],[f403,f42])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X3] : (~r2_hidden(X3,sK1) | sK1 = k1_relat_1(sK2) | r2_hidden(k4_tarski(X3,sK4(X3)),sK2)) )),
% 0.23/0.54    inference(backward_demodulation,[],[f14,f38])).
% 0.23/0.54  fof(f14,plain,(
% 0.23/0.54    ( ! [X3] : (sK1 = k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(X3,sK4(X3)),sK2)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f9])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (25460)------------------------------
% 0.23/0.54  % (25460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (25460)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (25460)Memory used [KB]: 1918
% 0.23/0.54  % (25460)Time elapsed: 0.073 s
% 0.23/0.54  % (25460)------------------------------
% 0.23/0.54  % (25460)------------------------------
% 0.23/0.54  % (25449)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.54  % (25445)Success in time 0.169 s
%------------------------------------------------------------------------------
