%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:40 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   49 (  70 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 150 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(resolution,[],[f161,f104])).

fof(f104,plain,(
    ! [X2] : r2_hidden(sK0,X2) ),
    inference(subsumption_resolution,[],[f101,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f101,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | r2_hidden(sK0,X2) ) ),
    inference(superposition,[],[f35,f82])).

fof(f82,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f80,f23])).

fof(f80,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ r1_tarski(k1_xboole_0,k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f161,plain,(
    ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f160,f133])).

fof(f133,plain,(
    ! [X5] : k1_xboole_0 != k1_tarski(X5) ),
    inference(superposition,[],[f45,f127])).

fof(f127,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(backward_demodulation,[],[f50,f126])).

fof(f126,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(subsumption_resolution,[],[f120,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f120,plain,(
    ! [X0] :
      ( k3_tarski(k1_tarski(X0)) = X0
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f50,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f28,f24])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X3] : k1_xboole_0 != k2_xboole_0(X3,k1_tarski(X2)) ),
    inference(superposition,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f160,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X6) ) ),
    inference(resolution,[],[f98,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f33,f23])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (804749313)
% 0.14/0.37  ipcrm: permission denied for id (806092802)
% 0.14/0.37  ipcrm: permission denied for id (804814851)
% 0.14/0.37  ipcrm: permission denied for id (806125572)
% 0.14/0.37  ipcrm: permission denied for id (806158341)
% 0.14/0.37  ipcrm: permission denied for id (804880390)
% 0.14/0.37  ipcrm: permission denied for id (804913159)
% 0.14/0.37  ipcrm: permission denied for id (806191112)
% 0.14/0.37  ipcrm: permission denied for id (809959433)
% 0.14/0.37  ipcrm: permission denied for id (806256650)
% 0.14/0.38  ipcrm: permission denied for id (806322188)
% 0.14/0.38  ipcrm: permission denied for id (804978701)
% 0.14/0.38  ipcrm: permission denied for id (810024974)
% 0.14/0.38  ipcrm: permission denied for id (805011471)
% 0.14/0.38  ipcrm: permission denied for id (810057744)
% 0.14/0.38  ipcrm: permission denied for id (810090513)
% 0.14/0.38  ipcrm: permission denied for id (806486034)
% 0.14/0.39  ipcrm: permission denied for id (806518803)
% 0.14/0.39  ipcrm: permission denied for id (806584341)
% 0.21/0.39  ipcrm: permission denied for id (806617110)
% 0.21/0.39  ipcrm: permission denied for id (806649879)
% 0.21/0.39  ipcrm: permission denied for id (806682648)
% 0.21/0.39  ipcrm: permission denied for id (810156057)
% 0.21/0.39  ipcrm: permission denied for id (806748186)
% 0.21/0.40  ipcrm: permission denied for id (806780955)
% 0.21/0.40  ipcrm: permission denied for id (806813724)
% 0.21/0.40  ipcrm: permission denied for id (806846493)
% 0.21/0.40  ipcrm: permission denied for id (810221599)
% 0.21/0.40  ipcrm: permission denied for id (806944800)
% 0.21/0.40  ipcrm: permission denied for id (805109793)
% 0.21/0.40  ipcrm: permission denied for id (806977570)
% 0.21/0.41  ipcrm: permission denied for id (807010339)
% 0.21/0.41  ipcrm: permission denied for id (807043108)
% 0.21/0.41  ipcrm: permission denied for id (807075877)
% 0.21/0.41  ipcrm: permission denied for id (807108646)
% 0.21/0.41  ipcrm: permission denied for id (807174183)
% 0.21/0.41  ipcrm: permission denied for id (807206952)
% 0.21/0.41  ipcrm: permission denied for id (810254377)
% 0.21/0.41  ipcrm: permission denied for id (810287146)
% 0.21/0.41  ipcrm: permission denied for id (807305259)
% 0.21/0.42  ipcrm: permission denied for id (807338028)
% 0.21/0.42  ipcrm: permission denied for id (805208109)
% 0.21/0.42  ipcrm: permission denied for id (807436334)
% 0.21/0.42  ipcrm: permission denied for id (807469103)
% 0.21/0.42  ipcrm: permission denied for id (807501872)
% 0.21/0.42  ipcrm: permission denied for id (810319921)
% 0.21/0.42  ipcrm: permission denied for id (807632947)
% 0.21/0.43  ipcrm: permission denied for id (807665716)
% 0.21/0.43  ipcrm: permission denied for id (805339190)
% 0.21/0.43  ipcrm: permission denied for id (807731255)
% 0.21/0.43  ipcrm: permission denied for id (807764024)
% 0.21/0.43  ipcrm: permission denied for id (807796793)
% 0.21/0.43  ipcrm: permission denied for id (807829562)
% 0.21/0.43  ipcrm: permission denied for id (807862331)
% 0.21/0.43  ipcrm: permission denied for id (805470268)
% 0.21/0.44  ipcrm: permission denied for id (805503037)
% 0.21/0.44  ipcrm: permission denied for id (807895102)
% 0.21/0.44  ipcrm: permission denied for id (805568575)
% 0.21/0.44  ipcrm: permission denied for id (807927872)
% 0.21/0.44  ipcrm: permission denied for id (805601345)
% 0.21/0.44  ipcrm: permission denied for id (807960642)
% 0.21/0.44  ipcrm: permission denied for id (807993411)
% 0.21/0.44  ipcrm: permission denied for id (808026180)
% 0.21/0.45  ipcrm: permission denied for id (810418245)
% 0.21/0.45  ipcrm: permission denied for id (808091718)
% 0.21/0.45  ipcrm: permission denied for id (808124487)
% 0.21/0.45  ipcrm: permission denied for id (810451016)
% 0.21/0.45  ipcrm: permission denied for id (810483785)
% 0.21/0.45  ipcrm: permission denied for id (808222794)
% 0.21/0.45  ipcrm: permission denied for id (808288332)
% 0.21/0.46  ipcrm: permission denied for id (808321101)
% 0.21/0.46  ipcrm: permission denied for id (808353870)
% 0.21/0.46  ipcrm: permission denied for id (810614865)
% 0.21/0.46  ipcrm: permission denied for id (810647634)
% 0.21/0.46  ipcrm: permission denied for id (808517715)
% 0.21/0.46  ipcrm: permission denied for id (805765204)
% 0.21/0.47  ipcrm: permission denied for id (810713174)
% 0.21/0.47  ipcrm: permission denied for id (808616023)
% 0.21/0.47  ipcrm: permission denied for id (805797976)
% 0.21/0.47  ipcrm: permission denied for id (810745945)
% 0.21/0.47  ipcrm: permission denied for id (808681562)
% 0.21/0.47  ipcrm: permission denied for id (808714331)
% 0.21/0.47  ipcrm: permission denied for id (810778716)
% 0.21/0.47  ipcrm: permission denied for id (810811485)
% 0.21/0.48  ipcrm: permission denied for id (808845406)
% 0.21/0.48  ipcrm: permission denied for id (810844255)
% 0.21/0.48  ipcrm: permission denied for id (808943713)
% 0.21/0.48  ipcrm: permission denied for id (809042019)
% 0.21/0.48  ipcrm: permission denied for id (809074788)
% 0.21/0.48  ipcrm: permission denied for id (809107557)
% 0.21/0.48  ipcrm: permission denied for id (810942566)
% 0.21/0.49  ipcrm: permission denied for id (811008104)
% 0.21/0.49  ipcrm: permission denied for id (809238633)
% 0.21/0.49  ipcrm: permission denied for id (809271402)
% 0.21/0.49  ipcrm: permission denied for id (809336940)
% 0.21/0.49  ipcrm: permission denied for id (809402478)
% 0.21/0.50  ipcrm: permission denied for id (809468016)
% 0.21/0.50  ipcrm: permission denied for id (805929074)
% 0.21/0.50  ipcrm: permission denied for id (809599093)
% 0.21/0.50  ipcrm: permission denied for id (809631862)
% 0.21/0.50  ipcrm: permission denied for id (811237495)
% 0.21/0.51  ipcrm: permission denied for id (809730169)
% 0.21/0.51  ipcrm: permission denied for id (811303034)
% 0.21/0.51  ipcrm: permission denied for id (805994620)
% 0.21/0.51  ipcrm: permission denied for id (809828477)
% 0.21/0.51  ipcrm: permission denied for id (806027390)
% 0.21/0.51  ipcrm: permission denied for id (809861247)
% 0.37/0.62  % (12130)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.37/0.64  % (12124)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.37/0.64  % (12131)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.37/0.64  % (12130)Refutation found. Thanks to Tanya!
% 0.37/0.64  % SZS status Theorem for theBenchmark
% 0.37/0.64  % SZS output start Proof for theBenchmark
% 0.37/0.64  fof(f165,plain,(
% 0.37/0.64    $false),
% 0.37/0.64    inference(resolution,[],[f161,f104])).
% 0.37/0.64  fof(f104,plain,(
% 0.37/0.64    ( ! [X2] : (r2_hidden(sK0,X2)) )),
% 0.37/0.64    inference(subsumption_resolution,[],[f101,f23])).
% 0.37/0.64  fof(f23,plain,(
% 0.37/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f4])).
% 0.37/0.64  fof(f4,axiom,(
% 0.37/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.37/0.64  fof(f101,plain,(
% 0.37/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | r2_hidden(sK0,X2)) )),
% 0.37/0.64    inference(superposition,[],[f35,f82])).
% 0.37/0.64  fof(f82,plain,(
% 0.37/0.64    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.37/0.64    inference(subsumption_resolution,[],[f80,f23])).
% 0.37/0.64  fof(f80,plain,(
% 0.37/0.64    k1_xboole_0 = k2_tarski(sK0,sK1) | ~r1_tarski(k1_xboole_0,k2_tarski(sK0,sK1))),
% 0.37/0.64    inference(resolution,[],[f33,f40])).
% 0.37/0.64  fof(f40,plain,(
% 0.37/0.64    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0)),
% 0.37/0.64    inference(superposition,[],[f25,f22])).
% 0.37/0.64  fof(f22,plain,(
% 0.37/0.64    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.37/0.64    inference(cnf_transformation,[],[f17])).
% 0.37/0.64  fof(f17,plain,(
% 0.37/0.64    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.37/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 0.37/0.64  fof(f16,plain,(
% 0.37/0.64    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.37/0.64    introduced(choice_axiom,[])).
% 0.37/0.64  fof(f14,plain,(
% 0.37/0.64    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.37/0.64    inference(ennf_transformation,[],[f13])).
% 0.37/0.64  fof(f13,negated_conjecture,(
% 0.37/0.64    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.37/0.64    inference(negated_conjecture,[],[f12])).
% 0.37/0.64  fof(f12,conjecture,(
% 0.37/0.64    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.37/0.64  fof(f25,plain,(
% 0.37/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.37/0.64    inference(cnf_transformation,[],[f5])).
% 0.37/0.64  fof(f5,axiom,(
% 0.37/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.37/0.64  fof(f33,plain,(
% 0.37/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f19])).
% 0.37/0.64  fof(f19,plain,(
% 0.37/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.37/0.64    inference(flattening,[],[f18])).
% 0.37/0.64  fof(f18,plain,(
% 0.37/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.37/0.64    inference(nnf_transformation,[],[f2])).
% 0.37/0.64  fof(f2,axiom,(
% 0.37/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.37/0.64  fof(f35,plain,(
% 0.37/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f21])).
% 0.37/0.64  fof(f21,plain,(
% 0.37/0.64    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.37/0.64    inference(flattening,[],[f20])).
% 0.37/0.64  fof(f20,plain,(
% 0.37/0.64    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.37/0.64    inference(nnf_transformation,[],[f10])).
% 0.37/0.64  fof(f10,axiom,(
% 0.37/0.64    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.37/0.64  fof(f161,plain,(
% 0.37/0.64    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) )),
% 0.37/0.64    inference(subsumption_resolution,[],[f160,f133])).
% 0.37/0.64  fof(f133,plain,(
% 0.37/0.64    ( ! [X5] : (k1_xboole_0 != k1_tarski(X5)) )),
% 0.37/0.64    inference(superposition,[],[f45,f127])).
% 0.37/0.64  fof(f127,plain,(
% 0.37/0.64    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.37/0.64    inference(backward_demodulation,[],[f50,f126])).
% 0.37/0.64  fof(f126,plain,(
% 0.37/0.64    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.37/0.64    inference(subsumption_resolution,[],[f120,f38])).
% 0.37/0.64  fof(f38,plain,(
% 0.37/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.37/0.64    inference(equality_resolution,[],[f32])).
% 0.37/0.64  fof(f32,plain,(
% 0.37/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.37/0.64    inference(cnf_transformation,[],[f19])).
% 0.37/0.64  fof(f120,plain,(
% 0.37/0.64    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0 | ~r1_tarski(X0,X0)) )),
% 0.37/0.64    inference(superposition,[],[f50,f30])).
% 0.37/0.64  fof(f30,plain,(
% 0.37/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f15])).
% 0.37/0.64  fof(f15,plain,(
% 0.37/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.37/0.64    inference(ennf_transformation,[],[f3])).
% 0.37/0.64  fof(f3,axiom,(
% 0.37/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.37/0.64  fof(f50,plain,(
% 0.37/0.64    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 0.37/0.64    inference(superposition,[],[f28,f24])).
% 0.37/0.64  fof(f24,plain,(
% 0.37/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f6])).
% 0.37/0.64  fof(f6,axiom,(
% 0.37/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.37/0.64  fof(f28,plain,(
% 0.37/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.37/0.64    inference(cnf_transformation,[],[f9])).
% 0.37/0.64  fof(f9,axiom,(
% 0.37/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.37/0.64  fof(f45,plain,(
% 0.37/0.64    ( ! [X2,X3] : (k1_xboole_0 != k2_xboole_0(X3,k1_tarski(X2))) )),
% 0.37/0.64    inference(superposition,[],[f26,f27])).
% 0.37/0.64  fof(f27,plain,(
% 0.37/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f1])).
% 0.37/0.64  fof(f1,axiom,(
% 0.37/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.37/0.64  fof(f26,plain,(
% 0.37/0.64    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f11])).
% 0.37/0.64  fof(f11,axiom,(
% 0.37/0.64    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.37/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.37/0.64  fof(f160,plain,(
% 0.37/0.64    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | k1_xboole_0 = k1_tarski(X6)) )),
% 0.37/0.64    inference(resolution,[],[f98,f76])).
% 0.37/0.64  fof(f76,plain,(
% 0.37/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.37/0.64    inference(resolution,[],[f33,f23])).
% 0.37/0.64  fof(f98,plain,(
% 0.37/0.64    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.37/0.64    inference(duplicate_literal_removal,[],[f97])).
% 0.37/0.64  fof(f97,plain,(
% 0.37/0.64    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.37/0.64    inference(superposition,[],[f37,f24])).
% 0.37/0.64  fof(f37,plain,(
% 0.37/0.64    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.37/0.64    inference(cnf_transformation,[],[f21])).
% 0.37/0.64  % SZS output end Proof for theBenchmark
% 0.37/0.64  % (12130)------------------------------
% 0.37/0.64  % (12130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.64  % (12130)Termination reason: Refutation
% 0.37/0.64  
% 0.37/0.64  % (12130)Memory used [KB]: 1791
% 0.37/0.64  % (12130)Time elapsed: 0.083 s
% 0.37/0.64  % (12130)------------------------------
% 0.37/0.64  % (12130)------------------------------
% 0.37/0.64  % (11987)Success in time 0.287 s
%------------------------------------------------------------------------------
