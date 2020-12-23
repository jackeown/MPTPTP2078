%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:50 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 (  98 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f17,f29,f63,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k9_relat_1(X0,k2_xboole_0(X1,X2)))
      | ~ r1_tarski(X3,k9_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f63,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f58,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f58,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f17,f24])).

fof(f35,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f18,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f26,f19])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f18,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

fof(f29,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:39:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (785874945)
% 0.14/0.38  ipcrm: permission denied for id (790265858)
% 0.14/0.38  ipcrm: permission denied for id (791773187)
% 0.14/0.38  ipcrm: permission denied for id (790331396)
% 0.14/0.38  ipcrm: permission denied for id (791805957)
% 0.14/0.38  ipcrm: permission denied for id (786333702)
% 0.14/0.38  ipcrm: permission denied for id (785907719)
% 0.14/0.38  ipcrm: permission denied for id (786366472)
% 0.14/0.38  ipcrm: permission denied for id (786399241)
% 0.14/0.38  ipcrm: permission denied for id (786432010)
% 0.14/0.39  ipcrm: permission denied for id (790396939)
% 0.14/0.39  ipcrm: permission denied for id (786497548)
% 0.14/0.39  ipcrm: permission denied for id (786530317)
% 0.14/0.39  ipcrm: permission denied for id (792821774)
% 0.14/0.39  ipcrm: permission denied for id (786595855)
% 0.14/0.39  ipcrm: permission denied for id (786628624)
% 0.14/0.39  ipcrm: permission denied for id (786661393)
% 0.21/0.39  ipcrm: permission denied for id (786694162)
% 0.21/0.40  ipcrm: permission denied for id (786726931)
% 0.21/0.40  ipcrm: permission denied for id (791871508)
% 0.21/0.40  ipcrm: permission denied for id (786792469)
% 0.21/0.40  ipcrm: permission denied for id (786858007)
% 0.21/0.40  ipcrm: permission denied for id (785940504)
% 0.21/0.40  ipcrm: permission denied for id (786890777)
% 0.21/0.41  ipcrm: permission denied for id (790560794)
% 0.21/0.41  ipcrm: permission denied for id (790593563)
% 0.21/0.41  ipcrm: permission denied for id (786989084)
% 0.21/0.41  ipcrm: permission denied for id (787021853)
% 0.21/0.41  ipcrm: permission denied for id (787054622)
% 0.21/0.41  ipcrm: permission denied for id (787087391)
% 0.21/0.41  ipcrm: permission denied for id (787120160)
% 0.21/0.41  ipcrm: permission denied for id (787152929)
% 0.21/0.42  ipcrm: permission denied for id (791937058)
% 0.21/0.42  ipcrm: permission denied for id (787218467)
% 0.21/0.42  ipcrm: permission denied for id (790659108)
% 0.21/0.42  ipcrm: permission denied for id (787284005)
% 0.21/0.42  ipcrm: permission denied for id (791969830)
% 0.21/0.42  ipcrm: permission denied for id (787349543)
% 0.21/0.42  ipcrm: permission denied for id (787382312)
% 0.21/0.42  ipcrm: permission denied for id (790724649)
% 0.21/0.43  ipcrm: permission denied for id (787447850)
% 0.21/0.43  ipcrm: permission denied for id (787480619)
% 0.21/0.43  ipcrm: permission denied for id (790757420)
% 0.21/0.43  ipcrm: permission denied for id (787546157)
% 0.21/0.43  ipcrm: permission denied for id (787578926)
% 0.21/0.43  ipcrm: permission denied for id (787611695)
% 0.21/0.43  ipcrm: permission denied for id (792002608)
% 0.21/0.43  ipcrm: permission denied for id (787677233)
% 0.21/0.44  ipcrm: permission denied for id (792035378)
% 0.21/0.44  ipcrm: permission denied for id (787742771)
% 0.21/0.44  ipcrm: permission denied for id (790855732)
% 0.21/0.44  ipcrm: permission denied for id (787808309)
% 0.21/0.44  ipcrm: permission denied for id (790888502)
% 0.21/0.44  ipcrm: permission denied for id (787873847)
% 0.21/0.44  ipcrm: permission denied for id (792068152)
% 0.21/0.44  ipcrm: permission denied for id (787939385)
% 0.21/0.45  ipcrm: permission denied for id (792100922)
% 0.21/0.45  ipcrm: permission denied for id (788004923)
% 0.21/0.45  ipcrm: permission denied for id (792133692)
% 0.21/0.45  ipcrm: permission denied for id (788070461)
% 0.21/0.45  ipcrm: permission denied for id (792166462)
% 0.21/0.45  ipcrm: permission denied for id (788135999)
% 0.21/0.45  ipcrm: permission denied for id (788168768)
% 0.21/0.45  ipcrm: permission denied for id (788201537)
% 0.21/0.46  ipcrm: permission denied for id (788234306)
% 0.21/0.46  ipcrm: permission denied for id (788267075)
% 0.21/0.46  ipcrm: permission denied for id (785973316)
% 0.21/0.46  ipcrm: permission denied for id (788299845)
% 0.21/0.46  ipcrm: permission denied for id (788332614)
% 0.21/0.46  ipcrm: permission denied for id (788365383)
% 0.21/0.46  ipcrm: permission denied for id (792887368)
% 0.21/0.46  ipcrm: permission denied for id (788430921)
% 0.21/0.46  ipcrm: permission denied for id (788463690)
% 0.21/0.47  ipcrm: permission denied for id (788496459)
% 0.21/0.47  ipcrm: permission denied for id (788529228)
% 0.21/0.47  ipcrm: permission denied for id (788561997)
% 0.21/0.47  ipcrm: permission denied for id (793903182)
% 0.21/0.47  ipcrm: permission denied for id (792952911)
% 0.21/0.47  ipcrm: permission denied for id (793575504)
% 0.21/0.47  ipcrm: permission denied for id (793935953)
% 0.21/0.48  ipcrm: permission denied for id (788725842)
% 0.21/0.48  ipcrm: permission denied for id (788758611)
% 0.21/0.48  ipcrm: permission denied for id (788791380)
% 0.21/0.48  ipcrm: permission denied for id (793051221)
% 0.21/0.48  ipcrm: permission denied for id (788856918)
% 0.21/0.48  ipcrm: permission denied for id (793968727)
% 0.21/0.48  ipcrm: permission denied for id (788922456)
% 0.21/0.48  ipcrm: permission denied for id (788955225)
% 0.21/0.49  ipcrm: permission denied for id (788987994)
% 0.21/0.49  ipcrm: permission denied for id (789020763)
% 0.21/0.49  ipcrm: permission denied for id (789053532)
% 0.21/0.49  ipcrm: permission denied for id (789086301)
% 0.21/0.49  ipcrm: permission denied for id (793116766)
% 0.21/0.49  ipcrm: permission denied for id (789151839)
% 0.21/0.49  ipcrm: permission denied for id (792461408)
% 0.21/0.49  ipcrm: permission denied for id (789217377)
% 0.21/0.50  ipcrm: permission denied for id (789282915)
% 0.21/0.50  ipcrm: permission denied for id (793182308)
% 0.21/0.50  ipcrm: permission denied for id (789348453)
% 0.21/0.50  ipcrm: permission denied for id (793706598)
% 0.21/0.50  ipcrm: permission denied for id (789413991)
% 0.21/0.50  ipcrm: permission denied for id (789446760)
% 0.21/0.50  ipcrm: permission denied for id (793247849)
% 0.21/0.51  ipcrm: permission denied for id (793280618)
% 0.21/0.51  ipcrm: permission denied for id (789545067)
% 0.21/0.51  ipcrm: permission denied for id (793313388)
% 0.21/0.51  ipcrm: permission denied for id (789610605)
% 0.21/0.51  ipcrm: permission denied for id (789643374)
% 0.21/0.51  ipcrm: permission denied for id (789676143)
% 0.21/0.51  ipcrm: permission denied for id (789708912)
% 0.34/0.51  ipcrm: permission denied for id (789741681)
% 0.34/0.52  ipcrm: permission denied for id (789774450)
% 0.34/0.52  ipcrm: permission denied for id (794034291)
% 0.34/0.52  ipcrm: permission denied for id (789839988)
% 0.34/0.52  ipcrm: permission denied for id (791576693)
% 0.34/0.52  ipcrm: permission denied for id (789905526)
% 0.34/0.52  ipcrm: permission denied for id (794067063)
% 0.34/0.52  ipcrm: permission denied for id (789971064)
% 0.34/0.52  ipcrm: permission denied for id (791642233)
% 0.34/0.53  ipcrm: permission denied for id (790036602)
% 0.34/0.53  ipcrm: permission denied for id (793804923)
% 0.34/0.53  ipcrm: permission denied for id (790102140)
% 0.34/0.53  ipcrm: permission denied for id (790134909)
% 0.34/0.53  ipcrm: permission denied for id (791707774)
% 0.34/0.53  ipcrm: permission denied for id (790200447)
% 0.39/0.66  % (17989)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.39/0.66  % (17989)Refutation found. Thanks to Tanya!
% 0.39/0.66  % SZS status Theorem for theBenchmark
% 0.39/0.66  % SZS output start Proof for theBenchmark
% 0.39/0.66  fof(f69,plain,(
% 0.39/0.66    $false),
% 0.39/0.66    inference(unit_resulting_resolution,[],[f17,f29,f63,f37])).
% 0.39/0.66  fof(f37,plain,(
% 0.39/0.66    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k9_relat_1(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X3,k9_relat_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 0.39/0.66    inference(superposition,[],[f25,f24])).
% 0.39/0.66  fof(f24,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f10])).
% 0.39/0.66  fof(f10,plain,(
% 0.39/0.66    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.39/0.66    inference(ennf_transformation,[],[f6])).
% 0.39/0.66  fof(f6,axiom,(
% 0.39/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.39/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 0.39/0.66  fof(f25,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f11])).
% 0.39/0.66  fof(f11,plain,(
% 0.39/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.39/0.66    inference(ennf_transformation,[],[f2])).
% 0.39/0.66  fof(f2,axiom,(
% 0.39/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.39/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.39/0.66  fof(f63,plain,(
% 0.39/0.66    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,sK0)))),
% 0.39/0.66    inference(forward_demodulation,[],[f58,f27])).
% 0.39/0.66  fof(f27,plain,(
% 0.39/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.39/0.66    inference(definition_unfolding,[],[f20,f19])).
% 0.39/0.66  fof(f19,plain,(
% 0.39/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f5])).
% 0.39/0.66  fof(f5,axiom,(
% 0.39/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.39/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.39/0.66  fof(f20,plain,(
% 0.39/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f3])).
% 0.39/0.66  fof(f3,axiom,(
% 0.39/0.66    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.39/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.39/0.66  fof(f58,plain,(
% 0.39/0.66    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))),
% 0.39/0.66    inference(backward_demodulation,[],[f35,f36])).
% 0.39/0.66  fof(f36,plain,(
% 0.39/0.66    ( ! [X0,X1] : (k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.39/0.66    inference(unit_resulting_resolution,[],[f17,f24])).
% 0.39/0.66  fof(f35,plain,(
% 0.39/0.66    ~r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k6_subset_1(sK0,sK1))))),
% 0.39/0.66    inference(unit_resulting_resolution,[],[f18,f28])).
% 0.39/0.66  fof(f28,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.39/0.66    inference(definition_unfolding,[],[f26,f19])).
% 0.39/0.66  fof(f26,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.39/0.66    inference(cnf_transformation,[],[f12])).
% 0.39/0.66  fof(f12,plain,(
% 0.39/0.66    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.39/0.66    inference(ennf_transformation,[],[f4])).
% 0.39/0.66  fof(f4,axiom,(
% 0.39/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.39/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.39/0.66  fof(f18,plain,(
% 0.39/0.66    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 0.39/0.66    inference(cnf_transformation,[],[f14])).
% 0.39/0.66  fof(f14,plain,(
% 0.39/0.66    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 0.39/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.39/0.66  fof(f13,plain,(
% 0.39/0.66    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 0.39/0.66    introduced(choice_axiom,[])).
% 0.39/0.66  fof(f9,plain,(
% 0.39/0.66    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 0.39/0.66    inference(ennf_transformation,[],[f8])).
% 0.39/0.66  fof(f8,negated_conjecture,(
% 0.39/0.66    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.39/0.66    inference(negated_conjecture,[],[f7])).
% 0.39/0.66  fof(f7,conjecture,(
% 0.39/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.39/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).
% 0.39/0.66  fof(f29,plain,(
% 0.39/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.39/0.66    inference(equality_resolution,[],[f22])).
% 0.39/0.66  fof(f22,plain,(
% 0.39/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.39/0.66    inference(cnf_transformation,[],[f16])).
% 0.39/0.66  fof(f16,plain,(
% 0.39/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.39/0.66    inference(flattening,[],[f15])).
% 0.39/0.66  fof(f15,plain,(
% 0.39/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.39/0.66    inference(nnf_transformation,[],[f1])).
% 0.39/0.66  fof(f1,axiom,(
% 0.39/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.39/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.39/0.66  fof(f17,plain,(
% 0.39/0.66    v1_relat_1(sK2)),
% 0.39/0.66    inference(cnf_transformation,[],[f14])).
% 0.39/0.66  % SZS output end Proof for theBenchmark
% 0.39/0.66  % (17989)------------------------------
% 0.39/0.66  % (17989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.66  % (17989)Termination reason: Refutation
% 0.39/0.66  
% 0.39/0.66  % (17989)Memory used [KB]: 1791
% 0.39/0.66  % (17989)Time elapsed: 0.083 s
% 0.39/0.66  % (17989)------------------------------
% 0.39/0.66  % (17989)------------------------------
% 0.39/0.66  % (17846)Success in time 0.29 s
%------------------------------------------------------------------------------
