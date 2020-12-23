%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:03 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  79 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 ( 118 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(subsumption_resolution,[],[f104,f74])).

fof(f74,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f29,f40])).

fof(f40,plain,(
    sK0 = sK2 ),
    inference(unit_resulting_resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f24,f19])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f30,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f29,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f18,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,(
    k2_tarski(sK0,sK1) = k2_tarski(sK0,sK0) ),
    inference(superposition,[],[f82,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f35,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X0)) ),
    inference(definition_unfolding,[],[f26,f27,f27])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

fof(f82,plain,(
    k2_tarski(sK0,sK0) = k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK0)) ),
    inference(superposition,[],[f76,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X3)) ),
    inference(definition_unfolding,[],[f25,f27,f27])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(f76,plain,(
    k2_tarski(sK0,sK0) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f73,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f73,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f30,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:49:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.36  ipcrm: permission denied for id (828440577)
% 0.22/0.37  ipcrm: permission denied for id (828473346)
% 0.22/0.37  ipcrm: permission denied for id (824836100)
% 0.22/0.37  ipcrm: permission denied for id (823459845)
% 0.22/0.37  ipcrm: permission denied for id (828538886)
% 0.22/0.37  ipcrm: permission denied for id (830472199)
% 0.22/0.37  ipcrm: permission denied for id (824934408)
% 0.22/0.38  ipcrm: permission denied for id (823525386)
% 0.22/0.38  ipcrm: permission denied for id (824999947)
% 0.22/0.38  ipcrm: permission denied for id (828637196)
% 0.22/0.38  ipcrm: permission denied for id (825065485)
% 0.22/0.38  ipcrm: permission denied for id (825098254)
% 0.22/0.38  ipcrm: permission denied for id (825163792)
% 0.22/0.38  ipcrm: permission denied for id (825229330)
% 0.22/0.39  ipcrm: permission denied for id (825294868)
% 0.22/0.39  ipcrm: permission denied for id (825360405)
% 0.22/0.39  ipcrm: permission denied for id (825393174)
% 0.22/0.39  ipcrm: permission denied for id (825425943)
% 0.22/0.39  ipcrm: permission denied for id (828768280)
% 0.22/0.39  ipcrm: permission denied for id (823689241)
% 0.22/0.39  ipcrm: permission denied for id (828801050)
% 0.22/0.40  ipcrm: permission denied for id (823722011)
% 0.22/0.40  ipcrm: permission denied for id (828833820)
% 0.22/0.40  ipcrm: permission denied for id (825557021)
% 0.22/0.40  ipcrm: permission denied for id (830636062)
% 0.22/0.40  ipcrm: permission denied for id (825622559)
% 0.22/0.40  ipcrm: permission denied for id (825655328)
% 0.22/0.40  ipcrm: permission denied for id (825688097)
% 0.22/0.41  ipcrm: permission denied for id (825720866)
% 0.22/0.41  ipcrm: permission denied for id (823820324)
% 0.22/0.41  ipcrm: permission denied for id (828932133)
% 0.22/0.41  ipcrm: permission denied for id (828964902)
% 0.22/0.41  ipcrm: permission denied for id (825851943)
% 0.22/0.41  ipcrm: permission denied for id (825884712)
% 0.22/0.41  ipcrm: permission denied for id (828997673)
% 0.22/0.41  ipcrm: permission denied for id (825950250)
% 0.22/0.42  ipcrm: permission denied for id (826015788)
% 0.22/0.42  ipcrm: permission denied for id (823918637)
% 0.22/0.42  ipcrm: permission denied for id (826048558)
% 0.22/0.42  ipcrm: permission denied for id (826081327)
% 0.22/0.42  ipcrm: permission denied for id (826114096)
% 0.22/0.42  ipcrm: permission denied for id (829063217)
% 0.22/0.42  ipcrm: permission denied for id (824016946)
% 0.22/0.43  ipcrm: permission denied for id (824049715)
% 0.22/0.43  ipcrm: permission denied for id (826212405)
% 0.22/0.43  ipcrm: permission denied for id (826245174)
% 0.22/0.43  ipcrm: permission denied for id (829128759)
% 0.22/0.43  ipcrm: permission denied for id (826310712)
% 0.22/0.43  ipcrm: permission denied for id (829161529)
% 0.22/0.43  ipcrm: permission denied for id (829194298)
% 0.22/0.44  ipcrm: permission denied for id (824082491)
% 0.22/0.44  ipcrm: permission denied for id (826409020)
% 0.22/0.44  ipcrm: permission denied for id (826441789)
% 0.22/0.44  ipcrm: permission denied for id (829227070)
% 0.22/0.44  ipcrm: permission denied for id (829259839)
% 0.22/0.44  ipcrm: permission denied for id (829292608)
% 0.22/0.44  ipcrm: permission denied for id (830767169)
% 0.22/0.44  ipcrm: permission denied for id (829423682)
% 0.22/0.45  ipcrm: permission denied for id (826671171)
% 0.22/0.45  ipcrm: permission denied for id (830799940)
% 0.22/0.45  ipcrm: permission denied for id (824180805)
% 0.22/0.45  ipcrm: permission denied for id (824213574)
% 0.22/0.45  ipcrm: permission denied for id (826736711)
% 0.22/0.45  ipcrm: permission denied for id (826769480)
% 0.22/0.45  ipcrm: permission denied for id (830865482)
% 0.22/0.45  ipcrm: permission denied for id (826867787)
% 0.22/0.46  ipcrm: permission denied for id (829521996)
% 0.22/0.46  ipcrm: permission denied for id (830898253)
% 0.22/0.46  ipcrm: permission denied for id (830931022)
% 0.22/0.46  ipcrm: permission denied for id (824279119)
% 0.22/0.46  ipcrm: permission denied for id (829620304)
% 0.22/0.46  ipcrm: permission denied for id (824311889)
% 0.22/0.46  ipcrm: permission denied for id (829685843)
% 0.22/0.47  ipcrm: permission denied for id (829718612)
% 0.22/0.47  ipcrm: permission denied for id (827129941)
% 0.22/0.47  ipcrm: permission denied for id (827162710)
% 0.22/0.47  ipcrm: permission denied for id (829751383)
% 0.22/0.47  ipcrm: permission denied for id (830996568)
% 0.22/0.47  ipcrm: permission denied for id (827261017)
% 0.22/0.47  ipcrm: permission denied for id (827293786)
% 0.22/0.48  ipcrm: permission denied for id (827359324)
% 0.22/0.48  ipcrm: permission denied for id (824410205)
% 0.22/0.48  ipcrm: permission denied for id (827392094)
% 0.22/0.48  ipcrm: permission denied for id (827424863)
% 0.22/0.48  ipcrm: permission denied for id (824475744)
% 0.22/0.48  ipcrm: permission denied for id (831062113)
% 0.22/0.48  ipcrm: permission denied for id (827490402)
% 0.22/0.48  ipcrm: permission denied for id (831094883)
% 0.22/0.49  ipcrm: permission denied for id (827555940)
% 0.22/0.49  ipcrm: permission denied for id (831127653)
% 0.22/0.49  ipcrm: permission denied for id (827621478)
% 0.22/0.49  ipcrm: permission denied for id (827654247)
% 0.22/0.49  ipcrm: permission denied for id (827687016)
% 0.22/0.49  ipcrm: permission denied for id (827719785)
% 0.22/0.49  ipcrm: permission denied for id (829980779)
% 0.22/0.50  ipcrm: permission denied for id (827818092)
% 0.22/0.50  ipcrm: permission denied for id (831193197)
% 0.22/0.50  ipcrm: permission denied for id (830111856)
% 0.22/0.50  ipcrm: permission denied for id (827981937)
% 0.22/0.50  ipcrm: permission denied for id (828014706)
% 0.22/0.50  ipcrm: permission denied for id (831357043)
% 0.22/0.50  ipcrm: permission denied for id (828080244)
% 0.22/0.51  ipcrm: permission denied for id (824574069)
% 0.22/0.51  ipcrm: permission denied for id (830210167)
% 0.22/0.51  ipcrm: permission denied for id (831422585)
% 0.22/0.51  ipcrm: permission denied for id (831455354)
% 0.22/0.51  ipcrm: permission denied for id (831520892)
% 0.22/0.52  ipcrm: permission denied for id (828342397)
% 0.22/0.52  ipcrm: permission denied for id (828375166)
% 0.22/0.52  ipcrm: permission denied for id (824672383)
% 0.65/0.65  % (24494)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.19/0.65  % (24510)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.19/0.65  % (24494)Refutation found. Thanks to Tanya!
% 1.19/0.65  % SZS status Theorem for theBenchmark
% 1.19/0.65  % SZS output start Proof for theBenchmark
% 1.19/0.65  fof(f110,plain,(
% 1.19/0.65    $false),
% 1.19/0.65    inference(subsumption_resolution,[],[f104,f74])).
% 1.19/0.65  fof(f74,plain,(
% 1.19/0.65    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK0)),
% 1.19/0.65    inference(backward_demodulation,[],[f29,f40])).
% 1.19/0.65  fof(f40,plain,(
% 1.19/0.65    sK0 = sK2),
% 1.19/0.65    inference(unit_resulting_resolution,[],[f30,f33])).
% 1.19/0.65  fof(f33,plain,(
% 1.19/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)) | X0 = X2) )),
% 1.19/0.65    inference(definition_unfolding,[],[f24,f19])).
% 1.19/0.65  fof(f19,plain,(
% 1.19/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.19/0.65    inference(cnf_transformation,[],[f5])).
% 1.19/0.65  fof(f5,axiom,(
% 1.19/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.19/0.65  fof(f24,plain,(
% 1.19/0.65    ( ! [X2,X0,X1] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.19/0.65    inference(cnf_transformation,[],[f13])).
% 1.19/0.65  fof(f13,plain,(
% 1.19/0.65    ! [X0,X1,X2] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.19/0.65    inference(ennf_transformation,[],[f8])).
% 1.19/0.65  fof(f8,axiom,(
% 1.19/0.65    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 1.19/0.65  fof(f30,plain,(
% 1.19/0.65    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))),
% 1.19/0.65    inference(definition_unfolding,[],[f17,f19])).
% 1.19/0.65  fof(f17,plain,(
% 1.19/0.65    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.19/0.65    inference(cnf_transformation,[],[f15])).
% 1.19/0.65  fof(f15,plain,(
% 1.19/0.65    k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).
% 1.19/0.65  fof(f14,plain,(
% 1.19/0.65    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 1.19/0.65    introduced(choice_axiom,[])).
% 1.19/0.65  fof(f11,plain,(
% 1.19/0.65    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.19/0.65    inference(ennf_transformation,[],[f10])).
% 1.19/0.65  fof(f10,negated_conjecture,(
% 1.19/0.65    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.19/0.65    inference(negated_conjecture,[],[f9])).
% 1.19/0.65  fof(f9,conjecture,(
% 1.19/0.65    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 1.19/0.65  fof(f29,plain,(
% 1.19/0.65    k2_tarski(sK0,sK1) != k2_tarski(sK2,sK2)),
% 1.19/0.65    inference(definition_unfolding,[],[f18,f19])).
% 1.19/0.65  fof(f18,plain,(
% 1.19/0.65    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 1.19/0.65    inference(cnf_transformation,[],[f15])).
% 1.19/0.65  fof(f104,plain,(
% 1.19/0.65    k2_tarski(sK0,sK1) = k2_tarski(sK0,sK0)),
% 1.19/0.65    inference(superposition,[],[f82,f55])).
% 1.19/0.65  fof(f55,plain,(
% 1.19/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X0))) )),
% 1.19/0.65    inference(superposition,[],[f35,f28])).
% 1.19/0.65  fof(f28,plain,(
% 1.19/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 1.19/0.65    inference(definition_unfolding,[],[f20,f27])).
% 1.19/0.65  fof(f27,plain,(
% 1.19/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.19/0.65    inference(cnf_transformation,[],[f4])).
% 1.19/0.65  fof(f4,axiom,(
% 1.19/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).
% 1.19/0.65  fof(f20,plain,(
% 1.19/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.19/0.65    inference(cnf_transformation,[],[f6])).
% 1.19/0.65  fof(f6,axiom,(
% 1.19/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.19/0.65  fof(f35,plain,(
% 1.19/0.65    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X0))) )),
% 1.19/0.65    inference(definition_unfolding,[],[f26,f27,f27])).
% 1.19/0.65  fof(f26,plain,(
% 1.19/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)) )),
% 1.19/0.65    inference(cnf_transformation,[],[f3])).
% 1.19/0.65  fof(f3,axiom,(
% 1.19/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 1.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
% 1.19/0.65  fof(f82,plain,(
% 1.19/0.65    k2_tarski(sK0,sK0) = k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK0))),
% 1.19/0.65    inference(superposition,[],[f76,f34])).
% 1.19/0.65  fof(f34,plain,(
% 1.19/0.65    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X3))) )),
% 1.19/0.65    inference(definition_unfolding,[],[f25,f27,f27])).
% 1.19/0.65  fof(f25,plain,(
% 1.19/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 1.19/0.65    inference(cnf_transformation,[],[f2])).
% 1.19/0.65  fof(f2,axiom,(
% 1.19/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 1.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 1.19/0.65  fof(f76,plain,(
% 1.19/0.65    k2_tarski(sK0,sK0) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),
% 1.19/0.65    inference(unit_resulting_resolution,[],[f73,f21])).
% 1.19/0.65  fof(f21,plain,(
% 1.19/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.19/0.65    inference(cnf_transformation,[],[f12])).
% 1.19/0.65  fof(f12,plain,(
% 1.19/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.19/0.65    inference(ennf_transformation,[],[f1])).
% 1.19/0.65  fof(f1,axiom,(
% 1.19/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.19/0.65  fof(f73,plain,(
% 1.19/0.65    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),
% 1.19/0.65    inference(backward_demodulation,[],[f30,f40])).
% 1.19/0.65  % SZS output end Proof for theBenchmark
% 1.19/0.65  % (24494)------------------------------
% 1.19/0.65  % (24494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.65  % (24494)Termination reason: Refutation
% 1.19/0.65  
% 1.19/0.65  % (24494)Memory used [KB]: 1791
% 1.19/0.65  % (24494)Time elapsed: 0.086 s
% 1.19/0.65  % (24494)------------------------------
% 1.19/0.65  % (24494)------------------------------
% 1.19/0.65  % (24355)Success in time 0.293 s
%------------------------------------------------------------------------------
