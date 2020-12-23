%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:04 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   39 (  66 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 186 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(subsumption_resolution,[],[f62,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19,f18])).

% (26010)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (26009)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (26001)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% (26000)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (25997)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (26011)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (26013)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (26007)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f62,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f31,f30])).

% (26008)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f57,plain,(
    ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f56,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f55,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f55,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f53,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f53,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f52,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f26,f27])).

fof(f51,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    inference(resolution,[],[f25,f44])).

fof(f44,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:27:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1243316225)
% 0.13/0.37  ipcrm: permission denied for id (1243348994)
% 0.13/0.37  ipcrm: permission denied for id (1243381763)
% 0.13/0.37  ipcrm: permission denied for id (1243414532)
% 0.13/0.38  ipcrm: permission denied for id (1243447301)
% 0.13/0.38  ipcrm: permission denied for id (1243545608)
% 0.20/0.38  ipcrm: permission denied for id (1243578377)
% 0.20/0.38  ipcrm: permission denied for id (1243742221)
% 0.20/0.39  ipcrm: permission denied for id (1243807759)
% 0.20/0.39  ipcrm: permission denied for id (1243873298)
% 0.20/0.39  ipcrm: permission denied for id (1243938836)
% 0.20/0.39  ipcrm: permission denied for id (1243971605)
% 0.20/0.40  ipcrm: permission denied for id (1244004374)
% 0.20/0.40  ipcrm: permission denied for id (1244037143)
% 0.20/0.40  ipcrm: permission denied for id (1244069912)
% 0.20/0.40  ipcrm: permission denied for id (1244102681)
% 0.20/0.40  ipcrm: permission denied for id (1244135450)
% 0.20/0.41  ipcrm: permission denied for id (1244332066)
% 0.20/0.41  ipcrm: permission denied for id (1244364835)
% 0.20/0.41  ipcrm: permission denied for id (1244430373)
% 0.20/0.41  ipcrm: permission denied for id (1244463142)
% 0.20/0.42  ipcrm: permission denied for id (1244528681)
% 0.20/0.42  ipcrm: permission denied for id (1244561450)
% 0.20/0.42  ipcrm: permission denied for id (1244725295)
% 0.20/0.43  ipcrm: permission denied for id (1244758064)
% 0.20/0.43  ipcrm: permission denied for id (1244790833)
% 0.20/0.43  ipcrm: permission denied for id (1244856371)
% 0.20/0.43  ipcrm: permission denied for id (1245020216)
% 0.20/0.44  ipcrm: permission denied for id (1245052985)
% 0.20/0.44  ipcrm: permission denied for id (1245085754)
% 0.20/0.44  ipcrm: permission denied for id (1245151292)
% 0.20/0.44  ipcrm: permission denied for id (1245184061)
% 0.20/0.44  ipcrm: permission denied for id (1245216830)
% 0.20/0.44  ipcrm: permission denied for id (1245282368)
% 0.20/0.45  ipcrm: permission denied for id (1245347906)
% 0.20/0.45  ipcrm: permission denied for id (1245380675)
% 0.20/0.45  ipcrm: permission denied for id (1245478982)
% 0.20/0.45  ipcrm: permission denied for id (1245544520)
% 0.20/0.45  ipcrm: permission denied for id (1245577289)
% 0.20/0.46  ipcrm: permission denied for id (1245642828)
% 0.20/0.46  ipcrm: permission denied for id (1245708366)
% 0.20/0.46  ipcrm: permission denied for id (1245741135)
% 0.20/0.46  ipcrm: permission denied for id (1245806673)
% 0.20/0.47  ipcrm: permission denied for id (1245839442)
% 0.20/0.47  ipcrm: permission denied for id (1245904981)
% 0.20/0.47  ipcrm: permission denied for id (1245937750)
% 0.20/0.47  ipcrm: permission denied for id (1245970520)
% 0.20/0.47  ipcrm: permission denied for id (1246003289)
% 0.20/0.48  ipcrm: permission denied for id (1246101596)
% 0.20/0.48  ipcrm: permission denied for id (1246167135)
% 0.20/0.48  ipcrm: permission denied for id (1246232673)
% 0.20/0.49  ipcrm: permission denied for id (1246298211)
% 0.20/0.49  ipcrm: permission denied for id (1246330980)
% 0.20/0.49  ipcrm: permission denied for id (1246429288)
% 0.20/0.49  ipcrm: permission denied for id (1246462059)
% 0.20/0.50  ipcrm: permission denied for id (1246527597)
% 0.20/0.50  ipcrm: permission denied for id (1246560366)
% 0.20/0.50  ipcrm: permission denied for id (1246593136)
% 0.20/0.50  ipcrm: permission denied for id (1246625905)
% 0.20/0.50  ipcrm: permission denied for id (1246658674)
% 0.20/0.51  ipcrm: permission denied for id (1246756981)
% 0.20/0.51  ipcrm: permission denied for id (1246855289)
% 0.20/0.51  ipcrm: permission denied for id (1246920827)
% 0.20/0.52  ipcrm: permission denied for id (1246986365)
% 0.20/0.52  ipcrm: permission denied for id (1247019134)
% 0.20/0.52  ipcrm: permission denied for id (1247051903)
% 0.36/0.62  % (26006)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.36/0.62  % (25998)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.36/0.63  % (25999)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.36/0.63  % (25999)Refutation found. Thanks to Tanya!
% 0.36/0.63  % SZS status Theorem for theBenchmark
% 0.36/0.63  % SZS output start Proof for theBenchmark
% 0.36/0.63  fof(f64,plain,(
% 0.36/0.63    $false),
% 0.36/0.63    inference(subsumption_resolution,[],[f62,f22])).
% 0.36/0.63  fof(f22,plain,(
% 0.36/0.63    v1_relat_1(sK1)),
% 0.36/0.63    inference(cnf_transformation,[],[f20])).
% 0.36/0.63  fof(f20,plain,(
% 0.36/0.63    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.36/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19,f18])).
% 0.36/0.63  % (26010)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.36/0.63  % (26009)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.36/0.64  % (26001)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.36/0.64  % (26000)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.36/0.64  % (25997)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.36/0.65  % (26011)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.36/0.65  % (26013)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.36/0.65  % (26007)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.36/0.65  fof(f18,plain,(
% 0.36/0.65    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.36/0.65    introduced(choice_axiom,[])).
% 0.36/0.65  fof(f19,plain,(
% 0.36/0.65    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.36/0.65    introduced(choice_axiom,[])).
% 0.36/0.65  fof(f12,plain,(
% 0.36/0.65    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.36/0.65    inference(ennf_transformation,[],[f11])).
% 0.36/0.65  fof(f11,negated_conjecture,(
% 0.36/0.65    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.36/0.65    inference(negated_conjecture,[],[f10])).
% 0.36/0.65  fof(f10,conjecture,(
% 0.36/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.36/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 0.36/0.65  fof(f62,plain,(
% 0.36/0.65    ~v1_relat_1(sK1)),
% 0.36/0.65    inference(resolution,[],[f57,f40])).
% 0.36/0.65  fof(f40,plain,(
% 0.36/0.65    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X1,X0)) | ~v1_relat_1(X0)) )),
% 0.36/0.65    inference(superposition,[],[f39,f27])).
% 0.36/0.65  fof(f27,plain,(
% 0.36/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.36/0.65    inference(cnf_transformation,[],[f1])).
% 0.36/0.65  fof(f1,axiom,(
% 0.36/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.36/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.36/0.65  fof(f39,plain,(
% 0.36/0.65    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.36/0.65    inference(superposition,[],[f31,f30])).
% 0.36/0.65  % (26008)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.36/0.65  fof(f30,plain,(
% 0.36/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.36/0.65    inference(cnf_transformation,[],[f4])).
% 0.36/0.65  fof(f4,axiom,(
% 0.36/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.36/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.36/0.65  fof(f31,plain,(
% 0.36/0.65    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.36/0.65    inference(cnf_transformation,[],[f15])).
% 0.36/0.65  fof(f15,plain,(
% 0.36/0.65    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.36/0.65    inference(ennf_transformation,[],[f8])).
% 0.36/0.65  fof(f8,axiom,(
% 0.36/0.65    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.36/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.36/0.65  fof(f57,plain,(
% 0.36/0.65    ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.36/0.65    inference(subsumption_resolution,[],[f56,f21])).
% 0.36/0.65  fof(f21,plain,(
% 0.36/0.65    v1_relat_1(sK0)),
% 0.36/0.65    inference(cnf_transformation,[],[f20])).
% 0.36/0.65  fof(f56,plain,(
% 0.36/0.65    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.36/0.65    inference(subsumption_resolution,[],[f55,f26])).
% 0.36/0.65  fof(f26,plain,(
% 0.36/0.65    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.36/0.65    inference(cnf_transformation,[],[f2])).
% 0.36/0.65  fof(f2,axiom,(
% 0.36/0.65    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.36/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.36/0.65  fof(f55,plain,(
% 0.36/0.65    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(sK0)),
% 0.36/0.65    inference(duplicate_literal_removal,[],[f54])).
% 0.36/0.65  fof(f54,plain,(
% 0.36/0.65    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.36/0.65    inference(resolution,[],[f53,f25])).
% 0.36/0.65  fof(f25,plain,(
% 0.36/0.65    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.36/0.65    inference(cnf_transformation,[],[f14])).
% 0.36/0.65  fof(f14,plain,(
% 0.36/0.65    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.36/0.65    inference(flattening,[],[f13])).
% 0.36/0.65  fof(f13,plain,(
% 0.36/0.65    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.36/0.65    inference(ennf_transformation,[],[f9])).
% 0.36/0.65  fof(f9,axiom,(
% 0.36/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.36/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.36/0.65  fof(f53,plain,(
% 0.36/0.65    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.36/0.65    inference(subsumption_resolution,[],[f52,f22])).
% 0.36/0.65  fof(f52,plain,(
% 0.36/0.65    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 0.36/0.65    inference(subsumption_resolution,[],[f51,f34])).
% 0.36/0.65  fof(f34,plain,(
% 0.36/0.65    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.36/0.65    inference(superposition,[],[f26,f27])).
% 0.36/0.65  fof(f51,plain,(
% 0.36/0.65    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 0.36/0.65    inference(resolution,[],[f25,f44])).
% 0.36/0.65  fof(f44,plain,(
% 0.36/0.65    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 0.36/0.65    inference(resolution,[],[f33,f23])).
% 0.36/0.65  fof(f23,plain,(
% 0.36/0.65    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.36/0.65    inference(cnf_transformation,[],[f20])).
% 0.36/0.65  fof(f33,plain,(
% 0.36/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.36/0.65    inference(cnf_transformation,[],[f17])).
% 0.36/0.65  fof(f17,plain,(
% 0.36/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.36/0.65    inference(flattening,[],[f16])).
% 0.36/0.65  fof(f16,plain,(
% 0.36/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.36/0.65    inference(ennf_transformation,[],[f3])).
% 0.36/0.65  fof(f3,axiom,(
% 0.36/0.65    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.36/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.36/0.65  % SZS output end Proof for theBenchmark
% 0.36/0.65  % (25999)------------------------------
% 0.36/0.65  % (25999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.65  % (25999)Termination reason: Refutation
% 0.36/0.65  
% 0.36/0.65  % (25999)Memory used [KB]: 1663
% 0.36/0.65  % (25999)Time elapsed: 0.054 s
% 0.36/0.65  % (25999)------------------------------
% 0.36/0.65  % (25999)------------------------------
% 0.36/0.65  % (26007)Refutation not found, incomplete strategy% (26007)------------------------------
% 0.36/0.65  % (26007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.65  % (26007)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.65  
% 0.36/0.65  % (26007)Memory used [KB]: 10618
% 0.36/0.65  % (26007)Time elapsed: 0.089 s
% 0.36/0.65  % (26007)------------------------------
% 0.36/0.65  % (26007)------------------------------
% 0.36/0.66  % (25857)Success in time 0.292 s
%------------------------------------------------------------------------------
