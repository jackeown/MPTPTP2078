%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:05 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  85 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 187 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f363,plain,(
    $false ),
    inference(subsumption_resolution,[],[f362,f40])).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f362,plain,(
    v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f361,f279])).

fof(f279,plain,(
    r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f158,f137])).

fof(f137,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f21,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(f158,plain,(
    ! [X0] : r2_hidden(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f117,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f117,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f33,f87,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f87,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f55,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f55,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f23,f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f361,plain,
    ( ~ r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f360,f180])).

fof(f180,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k9_subset_1(sK0,X1,sK2))) ),
    inference(unit_resulting_resolution,[],[f45,f170,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f170,plain,(
    ! [X6] : r1_tarski(k9_subset_1(sK0,X6,sK2),X6) ),
    inference(superposition,[],[f33,f137])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f360,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))
    | ~ r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f86,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,
    ( ~ m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(forward_demodulation,[],[f81,f79])).

fof(f79,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f23,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f81,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))
    | ~ m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f22,f35])).

fof(f22,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.54  % (28091)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.47/0.56  % (28089)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.57  % (28107)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.57  % (28099)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.62/0.57  % (28097)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.62/0.57  % (28105)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.62/0.59  % (28083)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.62/0.61  % (28088)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.62/0.61  % (28090)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.62/0.61  % (28103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.62/0.61  % (28087)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.62/0.61  % (28106)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.62/0.62  % (28086)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.62/0.62  % (28100)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.62/0.62  % (28112)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.62/0.62  % (28092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.62/0.62  % (28108)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.62/0.62  % (28111)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.62/0.62  % (28098)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.62/0.62  % (28104)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.62/0.62  % (28102)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.62/0.63  % (28084)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.62/0.63  % (28095)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.62/0.63  % (28110)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.62/0.63  % (28085)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.62/0.64  % (28096)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.62/0.64  % (28094)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.62/0.64  % (28101)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.19/0.65  % (28109)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.19/0.65  % (28093)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.19/0.66  % (28102)Refutation found. Thanks to Tanya!
% 2.19/0.66  % SZS status Theorem for theBenchmark
% 2.19/0.66  % SZS output start Proof for theBenchmark
% 2.19/0.66  fof(f363,plain,(
% 2.19/0.66    $false),
% 2.19/0.66    inference(subsumption_resolution,[],[f362,f40])).
% 2.19/0.66  fof(f40,plain,(
% 2.19/0.66    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f9])).
% 2.19/0.66  fof(f9,axiom,(
% 2.19/0.66    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.19/0.66  fof(f362,plain,(
% 2.19/0.66    v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.19/0.66    inference(subsumption_resolution,[],[f361,f279])).
% 2.19/0.66  fof(f279,plain,(
% 2.19/0.66    r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 2.19/0.66    inference(superposition,[],[f158,f137])).
% 2.19/0.66  fof(f137,plain,(
% 2.19/0.66    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f21,f42])).
% 2.19/0.66  fof(f42,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.19/0.66    inference(definition_unfolding,[],[f34,f41])).
% 2.19/0.66  fof(f41,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f5])).
% 2.19/0.66  fof(f5,axiom,(
% 2.19/0.66    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.19/0.66  fof(f34,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f18])).
% 2.19/0.66  fof(f18,plain,(
% 2.19/0.66    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f10])).
% 2.19/0.66  fof(f10,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.19/0.66  fof(f21,plain,(
% 2.19/0.66    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.19/0.66    inference(cnf_transformation,[],[f13])).
% 2.19/0.66  fof(f13,plain,(
% 2.19/0.66    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f12])).
% 2.19/0.66  fof(f12,negated_conjecture,(
% 2.19/0.66    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 2.19/0.66    inference(negated_conjecture,[],[f11])).
% 2.19/0.66  fof(f11,conjecture,(
% 2.19/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).
% 2.19/0.66  fof(f158,plain,(
% 2.19/0.66    ( ! [X0] : (r2_hidden(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f117,f44])).
% 2.19/0.66  fof(f44,plain,(
% 2.19/0.66    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.19/0.66    inference(equality_resolution,[],[f26])).
% 2.19/0.66  fof(f26,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.19/0.66    inference(cnf_transformation,[],[f6])).
% 2.19/0.66  fof(f6,axiom,(
% 2.19/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.19/0.66  fof(f117,plain,(
% 2.19/0.66    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),sK0)) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f33,f87,f25])).
% 2.19/0.66  fof(f25,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f17])).
% 2.19/0.66  fof(f17,plain,(
% 2.19/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.19/0.66    inference(flattening,[],[f16])).
% 2.19/0.66  fof(f16,plain,(
% 2.19/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.19/0.66    inference(ennf_transformation,[],[f2])).
% 2.19/0.66  fof(f2,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.19/0.66  fof(f87,plain,(
% 2.19/0.66    r1_tarski(sK1,sK0)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f55,f43])).
% 2.19/0.66  fof(f43,plain,(
% 2.19/0.66    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.19/0.66    inference(equality_resolution,[],[f27])).
% 2.19/0.66  fof(f27,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.19/0.66    inference(cnf_transformation,[],[f6])).
% 2.19/0.66  fof(f55,plain,(
% 2.19/0.66    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f23,f40,f39])).
% 2.19/0.66  fof(f39,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f20])).
% 2.19/0.66  fof(f20,plain,(
% 2.19/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f7])).
% 2.19/0.66  fof(f7,axiom,(
% 2.19/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.19/0.66  fof(f23,plain,(
% 2.19/0.66    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.19/0.66    inference(cnf_transformation,[],[f13])).
% 2.19/0.66  fof(f33,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f4])).
% 2.19/0.66  fof(f4,axiom,(
% 2.19/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.19/0.66  fof(f361,plain,(
% 2.19/0.66    ~r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.19/0.66    inference(subsumption_resolution,[],[f360,f180])).
% 2.19/0.66  fof(f180,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k9_subset_1(sK0,X1,sK2)))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f45,f170,f24])).
% 2.19/0.66  fof(f24,plain,(
% 2.19/0.66    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f15])).
% 2.19/0.66  fof(f15,plain,(
% 2.19/0.66    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.19/0.66    inference(flattening,[],[f14])).
% 2.19/0.66  fof(f14,plain,(
% 2.19/0.66    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.19/0.66    inference(ennf_transformation,[],[f3])).
% 2.19/0.66  fof(f3,axiom,(
% 2.19/0.66    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).
% 2.19/0.66  fof(f170,plain,(
% 2.19/0.66    ( ! [X6] : (r1_tarski(k9_subset_1(sK0,X6,sK2),X6)) )),
% 2.19/0.66    inference(superposition,[],[f33,f137])).
% 2.19/0.66  fof(f45,plain,(
% 2.19/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.19/0.66    inference(equality_resolution,[],[f31])).
% 2.19/0.66  fof(f31,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.19/0.66    inference(cnf_transformation,[],[f1])).
% 2.19/0.66  fof(f1,axiom,(
% 2.19/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.19/0.66  fof(f360,plain,(
% 2.19/0.66    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) | ~r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.19/0.66    inference(resolution,[],[f86,f38])).
% 2.19/0.66  fof(f38,plain,(
% 2.19/0.66    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f20])).
% 2.19/0.66  fof(f86,plain,(
% 2.19/0.66    ~m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 2.19/0.66    inference(forward_demodulation,[],[f81,f79])).
% 2.19/0.66  fof(f79,plain,(
% 2.19/0.66    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f23,f35])).
% 2.19/0.66  fof(f35,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f19])).
% 2.19/0.66  fof(f19,plain,(
% 2.19/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f8])).
% 2.19/0.66  fof(f8,axiom,(
% 2.19/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.19/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.19/0.66  fof(f81,plain,(
% 2.19/0.66    ~r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) | ~m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 2.19/0.66    inference(superposition,[],[f22,f35])).
% 2.19/0.66  fof(f22,plain,(
% 2.19/0.66    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 2.19/0.66    inference(cnf_transformation,[],[f13])).
% 2.19/0.66  % SZS output end Proof for theBenchmark
% 2.19/0.66  % (28102)------------------------------
% 2.19/0.66  % (28102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (28102)Termination reason: Refutation
% 2.19/0.66  
% 2.19/0.66  % (28102)Memory used [KB]: 2046
% 2.19/0.66  % (28102)Time elapsed: 0.229 s
% 2.19/0.66  % (28102)------------------------------
% 2.19/0.66  % (28102)------------------------------
% 2.39/0.68  % (28082)Success in time 0.315 s
%------------------------------------------------------------------------------
