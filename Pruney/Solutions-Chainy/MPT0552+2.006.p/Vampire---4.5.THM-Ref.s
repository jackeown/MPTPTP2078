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
% DateTime   : Thu Dec  3 12:49:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 116 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   19
%              Number of atoms          :  144 ( 290 expanded)
%              Number of equality atoms :    9 (  20 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(subsumption_resolution,[],[f106,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f106,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f105,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f105,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f100,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f100,plain,(
    ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f99,f27])).

fof(f99,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f98,f52])).

fof(f52,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f32,f49])).

fof(f49,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f45,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f98,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f95,f40])).

fof(f95,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))
    | ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f94,f27])).

fof(f94,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))
    | ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))
    | ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f92,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X2,X3))
      | ~ r1_tarski(k7_relat_1(X0,X1),k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f70,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1))
      | ~ r1_tarski(X2,k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f69,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1))
      | ~ r1_tarski(X2,k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f66,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f31,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1))
      | ~ r1_tarski(X2,k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f30,f37])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f92,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f91,f27])).

fof(f91,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:45:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (28719)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (28705)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (28717)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (28715)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (28712)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (28710)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (28720)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (28708)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (28709)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (28708)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f106,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f12])).
% 0.22/0.49  fof(f12,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f105,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(resolution,[],[f100,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f99,f27])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f98,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) )),
% 0.22/0.49    inference(superposition,[],[f32,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.22/0.49    inference(superposition,[],[f45,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.22/0.49    inference(superposition,[],[f35,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(resolution,[],[f95,f40])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) | ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f94,f27])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) | ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) | ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(resolution,[],[f92,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X2,X3)) | ~r1_tarski(k7_relat_1(X0,X1),k7_relat_1(X2,X3)) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(superposition,[],[f70,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1)) | ~r1_tarski(X2,k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1)) | ~r1_tarski(X2,k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.22/0.49    inference(resolution,[],[f31,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1)) | ~r1_tarski(X2,k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(superposition,[],[f30,f37])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) | ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f27])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 0.22/0.49    inference(resolution,[],[f75,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 0.22/0.49    inference(resolution,[],[f41,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (28708)------------------------------
% 0.22/0.49  % (28708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28708)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (28708)Memory used [KB]: 1663
% 0.22/0.49  % (28708)Time elapsed: 0.070 s
% 0.22/0.49  % (28708)------------------------------
% 0.22/0.49  % (28708)------------------------------
% 0.22/0.49  % (28704)Success in time 0.13 s
%------------------------------------------------------------------------------
