%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 253 expanded)
%              Number of leaves         :    8 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  125 (1027 expanded)
%              Number of equality atoms :   15 ( 169 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f101,f72])).

fof(f72,plain,(
    ~ r2_hidden(sK5(sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f40,f71,f24])).

fof(f24,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1)
        | k4_tarski(X4,X5) != sK0 )
    & r2_hidden(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1)
            | k4_tarski(X4,X5) != X0 )
        & r2_hidden(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ! [X5,X4] :
          ( ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1)
          | k4_tarski(X4,X5) != sK0 )
      & r2_hidden(sK0,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(f71,plain,(
    r2_hidden(sK4(sK0),sK1) ),
    inference(subsumption_resolution,[],[f70,f23])).

fof(f23,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,
    ( ~ r2_hidden(sK0,sK3)
    | r2_hidden(sK4(sK0),sK1) ),
    inference(superposition,[],[f68,f40])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK3)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f60,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

% (27070)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f59,f34])).

fof(f34,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f23,f22,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | v1_xboole_0(k2_zfmisc_1(sK1,sK2))
      | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f36,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f40,plain,(
    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) ),
    inference(unit_resulting_resolution,[],[f38,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f15,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f38,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f25])).

fof(f35,plain,(
    m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f23,f22,f26])).

fof(f101,plain,(
    r2_hidden(sK5(sK0),sK2) ),
    inference(subsumption_resolution,[],[f100,f23])).

fof(f100,plain,
    ( ~ r2_hidden(sK0,sK3)
    | r2_hidden(sK5(sK0),sK2) ),
    inference(superposition,[],[f69,f40])).

fof(f69,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X4),sK3)
      | r2_hidden(X4,sK2) ) ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:17:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (27063)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (27071)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (27062)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (27066)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (27071)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f101,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ~r2_hidden(sK5(sK0),sK2)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f40,f71,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X4,X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (! [X5,X4] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    r2_hidden(sK4(sK0),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f70,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    r2_hidden(sK0,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK3) | r2_hidden(sK4(sK0),sK1)),
% 0.22/0.51    inference(superposition,[],[f68,f40])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK3) | r2_hidden(X1,sK1)) )),
% 0.22/0.51    inference(resolution,[],[f60,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  % (27070)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f59,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f23,f22,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK3) | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | r2_hidden(X0,k2_zfmisc_1(sK1,sK2))) )),
% 0.22/0.51    inference(resolution,[],[f36,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f22,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    sK0 = k4_tarski(sK4(sK0),sK5(sK0))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f38,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK4(X0),sK5(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f15,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK4(X0),sK5(X0)) = X0)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f34,f35,f25])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f23,f22,f26])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    r2_hidden(sK5(sK0),sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f100,f23])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK3) | r2_hidden(sK5(sK0),sK2)),
% 0.22/0.51    inference(superposition,[],[f69,f40])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,X4),sK3) | r2_hidden(X4,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f60,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (27071)------------------------------
% 0.22/0.51  % (27071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27071)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (27071)Memory used [KB]: 6140
% 0.22/0.51  % (27071)Time elapsed: 0.070 s
% 0.22/0.51  % (27071)------------------------------
% 0.22/0.51  % (27071)------------------------------
% 0.22/0.51  % (27055)Success in time 0.147 s
%------------------------------------------------------------------------------
