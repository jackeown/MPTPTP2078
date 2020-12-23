%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 125 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 456 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25,f108])).

fof(f108,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK2,X0)) ),
    inference(forward_demodulation,[],[f107,f52])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f22,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
            & r1_tarski(X1,X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0))
          & r1_tarski(sK1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0))
        & r1_tarski(sK1,X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f107,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(sK2,X0)) ),
    inference(forward_demodulation,[],[f104,f53])).

fof(f53,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f23,f30])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK2,X0))) ),
    inference(unit_resulting_resolution,[],[f48,f49,f102,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f102,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f22,f23,f24,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f23,f39,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f22,f38,f28])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK1,X0),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f34,f33])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f22,f29])).

fof(f25,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (25998)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.46  % (25998)Refutation not found, incomplete strategy% (25998)------------------------------
% 0.20/0.46  % (25998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (25998)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (25998)Memory used [KB]: 10490
% 0.20/0.46  % (25998)Time elapsed: 0.053 s
% 0.20/0.46  % (25998)------------------------------
% 0.20/0.46  % (25998)------------------------------
% 0.20/0.47  % (26006)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.49  % (25990)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (25988)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (26000)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (26010)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (26011)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (26003)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.51  % (25989)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (26011)Refutation not found, incomplete strategy% (26011)------------------------------
% 0.20/0.51  % (26011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26011)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26011)Memory used [KB]: 10618
% 0.20/0.51  % (26011)Time elapsed: 0.094 s
% 0.20/0.51  % (26011)------------------------------
% 0.20/0.51  % (26011)------------------------------
% 0.20/0.51  % (25996)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (26002)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (25995)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (25995)Refutation not found, incomplete strategy% (25995)------------------------------
% 0.20/0.51  % (25995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25995)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25995)Memory used [KB]: 6012
% 0.20/0.51  % (25995)Time elapsed: 0.104 s
% 0.20/0.51  % (25995)------------------------------
% 0.20/0.51  % (25995)------------------------------
% 0.20/0.52  % (26004)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (26004)Refutation not found, incomplete strategy% (26004)------------------------------
% 0.20/0.52  % (26004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26004)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26004)Memory used [KB]: 1535
% 0.20/0.52  % (26004)Time elapsed: 0.103 s
% 0.20/0.52  % (26004)------------------------------
% 0.20/0.52  % (26004)------------------------------
% 0.20/0.52  % (25993)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.52  % (26002)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f25,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK2,X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f107,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f22,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ? [X2] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(sK2,X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f104,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f23,f30])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    v1_relat_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK2,X0)))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f48,f49,f102,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK2,X0))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f22,f23,f24,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f23,f39,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(sK2))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f35,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK2)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f23,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f22,f38,f28])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k7_relat_1(sK1,X0),k1_zfmisc_1(sK1))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f34,f33])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f22,f29])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (26002)------------------------------
% 0.20/0.52  % (26002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26002)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (26002)Memory used [KB]: 10618
% 0.20/0.52  % (26002)Time elapsed: 0.095 s
% 0.20/0.52  % (26002)------------------------------
% 0.20/0.52  % (26002)------------------------------
% 0.20/0.52  % (25987)Success in time 0.162 s
%------------------------------------------------------------------------------
