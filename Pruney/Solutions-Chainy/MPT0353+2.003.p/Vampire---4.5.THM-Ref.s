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
% DateTime   : Thu Dec  3 12:44:20 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 129 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  103 ( 306 expanded)
%              Number of equality atoms :   55 ( 131 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(subsumption_resolution,[],[f369,f206])).

fof(f206,plain,(
    ! [X3] : k4_xboole_0(sK1,X3) = k3_xboole_0(sK1,k4_xboole_0(sK0,X3)) ),
    inference(superposition,[],[f75,f192])).

fof(f192,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f188,f84])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f188,plain,(
    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f82,f176])).

fof(f176,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f166,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f166,plain,(
    r1_tarski(sK1,sK0) ),
    inference(superposition,[],[f103,f153])).

fof(f153,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f152,f126])).

fof(f126,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f122,f121])).

fof(f121,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f68,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f57,f56])).

fof(f56,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

% (12863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f35,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f34])).

fof(f34,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f122,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f68,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f152,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f147,f82])).

fof(f147,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f140,f79])).

fof(f140,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f137,f68])).

fof(f137,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f92,f121])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

% (12845)Refutation not found, incomplete strategy% (12845)------------------------------
% (12845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12845)Termination reason: Refutation not found, incomplete strategy

% (12845)Memory used [KB]: 10746
% (12845)Time elapsed: 0.127 s
% (12845)------------------------------
% (12845)------------------------------
fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f75,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f369,plain,(
    k4_xboole_0(sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f199,f83])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f199,plain,(
    k4_xboole_0(sK1,sK2) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f135,f124])).

% (12859)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f124,plain,(
    ! [X3] : k9_subset_1(sK0,sK1,X3) = k3_xboole_0(X3,sK1) ),
    inference(forward_demodulation,[],[f120,f119])).

fof(f119,plain,(
    ! [X2] : k9_subset_1(sK0,X2,sK1) = k3_xboole_0(X2,sK1) ),
    inference(resolution,[],[f68,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f120,plain,(
    ! [X3] : k9_subset_1(sK0,X3,sK1) = k9_subset_1(sK0,sK1,X3) ),
    inference(resolution,[],[f68,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f135,plain,(
    k4_xboole_0(sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f123,f131])).

fof(f131,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f69,f79])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f123,plain,(
    k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k4_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f70,f117])).

fof(f117,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0) ),
    inference(resolution,[],[f68,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f70,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (12861)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (12857)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (12838)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (12844)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.20/0.51  % (12840)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.20/0.52  % (12839)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.20/0.52  % (12837)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.20/0.52  % (12853)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.20/0.52  % (12849)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.52  % (12864)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.20/0.52  % (12836)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.20/0.53  % (12864)Refutation not found, incomplete strategy% (12864)------------------------------
% 1.20/0.53  % (12864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (12864)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (12864)Memory used [KB]: 1663
% 1.20/0.53  % (12864)Time elapsed: 0.080 s
% 1.20/0.53  % (12864)------------------------------
% 1.20/0.53  % (12864)------------------------------
% 1.20/0.53  % (12841)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.53  % (12848)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.20/0.53  % (12856)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.20/0.53  % (12860)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.20/0.53  % (12842)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.20/0.53  % (12847)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.20/0.53  % (12846)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.53  % (12862)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.54  % (12843)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.54  % (12849)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % (12845)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f371,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(subsumption_resolution,[],[f369,f206])).
% 1.41/0.54  fof(f206,plain,(
% 1.41/0.54    ( ! [X3] : (k4_xboole_0(sK1,X3) = k3_xboole_0(sK1,k4_xboole_0(sK0,X3))) )),
% 1.41/0.54    inference(superposition,[],[f75,f192])).
% 1.41/0.54  fof(f192,plain,(
% 1.41/0.54    sK1 = k3_xboole_0(sK1,sK0)),
% 1.41/0.54    inference(forward_demodulation,[],[f188,f84])).
% 1.41/0.54  fof(f84,plain,(
% 1.41/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,axiom,(
% 1.41/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.41/0.54  fof(f188,plain,(
% 1.41/0.54    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.41/0.54    inference(superposition,[],[f82,f176])).
% 1.41/0.54  fof(f176,plain,(
% 1.41/0.54    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.41/0.54    inference(resolution,[],[f166,f77])).
% 1.41/0.54  fof(f77,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f59])).
% 1.41/0.54  fof(f59,plain,(
% 1.41/0.54    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.41/0.54    inference(nnf_transformation,[],[f8])).
% 1.41/0.54  fof(f8,axiom,(
% 1.41/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.41/0.54  fof(f166,plain,(
% 1.41/0.54    r1_tarski(sK1,sK0)),
% 1.41/0.54    inference(superposition,[],[f103,f153])).
% 1.41/0.54  fof(f153,plain,(
% 1.41/0.54    sK1 = k3_xboole_0(sK0,sK1)),
% 1.41/0.54    inference(forward_demodulation,[],[f152,f126])).
% 1.41/0.54  fof(f126,plain,(
% 1.41/0.54    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 1.41/0.54    inference(forward_demodulation,[],[f122,f121])).
% 1.41/0.54  fof(f121,plain,(
% 1.41/0.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.41/0.54    inference(resolution,[],[f68,f79])).
% 1.41/0.54  fof(f79,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f42])).
% 1.41/0.54  fof(f42,plain,(
% 1.41/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f26])).
% 1.41/0.54  fof(f26,axiom,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.41/0.54  fof(f68,plain,(
% 1.41/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.41/0.54    inference(cnf_transformation,[],[f58])).
% 1.41/0.54  fof(f58,plain,(
% 1.41/0.54    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f57,f56])).
% 1.41/0.54  fof(f56,plain,(
% 1.41/0.54    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f57,plain,(
% 1.41/0.54    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f35])).
% 1.41/0.54  % (12863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.54  fof(f35,negated_conjecture,(
% 1.41/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.41/0.54    inference(negated_conjecture,[],[f34])).
% 1.41/0.54  fof(f34,conjecture,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 1.41/0.54  fof(f122,plain,(
% 1.41/0.54    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.41/0.54    inference(resolution,[],[f68,f78])).
% 1.41/0.54  fof(f78,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.41/0.54    inference(cnf_transformation,[],[f41])).
% 1.41/0.54  fof(f41,plain,(
% 1.41/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f29])).
% 1.41/0.54  fof(f29,axiom,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.41/0.54  fof(f152,plain,(
% 1.41/0.54    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)),
% 1.41/0.54    inference(forward_demodulation,[],[f147,f82])).
% 1.41/0.54  fof(f147,plain,(
% 1.41/0.54    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.41/0.54    inference(resolution,[],[f140,f79])).
% 1.41/0.54  fof(f140,plain,(
% 1.41/0.54    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.41/0.54    inference(subsumption_resolution,[],[f137,f68])).
% 1.41/0.54  fof(f137,plain,(
% 1.41/0.54    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.41/0.54    inference(superposition,[],[f92,f121])).
% 1.41/0.54  fof(f92,plain,(
% 1.41/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f49])).
% 1.41/0.54  % (12845)Refutation not found, incomplete strategy% (12845)------------------------------
% 1.41/0.54  % (12845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (12845)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (12845)Memory used [KB]: 10746
% 1.41/0.54  % (12845)Time elapsed: 0.127 s
% 1.41/0.54  % (12845)------------------------------
% 1.41/0.54  % (12845)------------------------------
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f27])).
% 1.41/0.54  fof(f27,axiom,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.41/0.54  fof(f103,plain,(
% 1.41/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.41/0.54  fof(f82,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f13])).
% 1.41/0.54  fof(f13,axiom,(
% 1.41/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.41/0.54  fof(f75,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f14])).
% 1.41/0.54  fof(f14,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.41/0.54  fof(f369,plain,(
% 1.41/0.54    k4_xboole_0(sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.41/0.54    inference(superposition,[],[f199,f83])).
% 1.41/0.54  fof(f83,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.41/0.54  fof(f199,plain,(
% 1.41/0.54    k4_xboole_0(sK1,sK2) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 1.41/0.54    inference(superposition,[],[f135,f124])).
% 1.41/0.54  % (12859)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.54  fof(f124,plain,(
% 1.41/0.54    ( ! [X3] : (k9_subset_1(sK0,sK1,X3) = k3_xboole_0(X3,sK1)) )),
% 1.41/0.54    inference(forward_demodulation,[],[f120,f119])).
% 1.41/0.54  fof(f119,plain,(
% 1.41/0.54    ( ! [X2] : (k9_subset_1(sK0,X2,sK1) = k3_xboole_0(X2,sK1)) )),
% 1.41/0.54    inference(resolution,[],[f68,f88])).
% 1.41/0.54  fof(f88,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f46])).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f31])).
% 1.41/0.54  fof(f31,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.41/0.54  fof(f120,plain,(
% 1.41/0.54    ( ! [X3] : (k9_subset_1(sK0,X3,sK1) = k9_subset_1(sK0,sK1,X3)) )),
% 1.41/0.54    inference(resolution,[],[f68,f87])).
% 1.41/0.54  fof(f87,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f45])).
% 1.41/0.54  fof(f45,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f25])).
% 1.41/0.54  fof(f25,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.41/0.54  fof(f135,plain,(
% 1.41/0.54    k4_xboole_0(sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))),
% 1.41/0.54    inference(backward_demodulation,[],[f123,f131])).
% 1.41/0.54  fof(f131,plain,(
% 1.41/0.54    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.41/0.54    inference(resolution,[],[f69,f79])).
% 1.41/0.54  fof(f69,plain,(
% 1.41/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.41/0.54    inference(cnf_transformation,[],[f58])).
% 1.41/0.54  fof(f123,plain,(
% 1.41/0.54    k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k4_xboole_0(sK1,sK2)),
% 1.41/0.54    inference(backward_demodulation,[],[f70,f117])).
% 1.41/0.54  fof(f117,plain,(
% 1.41/0.54    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0)) )),
% 1.41/0.54    inference(resolution,[],[f68,f93])).
% 1.41/0.54  fof(f93,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f50])).
% 1.41/0.54  fof(f50,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f30])).
% 1.41/0.54  fof(f30,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.41/0.54  fof(f70,plain,(
% 1.41/0.54    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.41/0.54    inference(cnf_transformation,[],[f58])).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (12849)------------------------------
% 1.41/0.54  % (12849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (12849)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (12849)Memory used [KB]: 1918
% 1.41/0.54  % (12849)Time elapsed: 0.089 s
% 1.41/0.54  % (12849)------------------------------
% 1.41/0.54  % (12849)------------------------------
% 1.41/0.54  % (12834)Success in time 0.182 s
%------------------------------------------------------------------------------
