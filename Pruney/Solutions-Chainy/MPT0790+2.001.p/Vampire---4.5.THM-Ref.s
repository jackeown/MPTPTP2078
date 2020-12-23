%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  34 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 100 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f21])).

fof(f21,plain,(
    k1_wellord1(sK1,sK0) != k1_wellord1(sK1,sK0) ),
    inference(superposition,[],[f14,f20])).

fof(f20,plain,(
    ! [X0] : k1_wellord1(sK1,X0) = k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0))) ),
    inference(global_subsumption,[],[f12,f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_wellord1(sK1,X0) = k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f18,f13])).

fof(f13,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | k1_wellord1(X0,X1) = k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X0,X1) = k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f16,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_relat_1(X1))
      | k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_wellord1)).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (803799040)
% 0.13/0.36  ipcrm: permission denied for id (803831810)
% 0.13/0.37  ipcrm: permission denied for id (803864580)
% 0.13/0.37  ipcrm: permission denied for id (803930118)
% 0.13/0.37  ipcrm: permission denied for id (803995657)
% 0.13/0.39  ipcrm: permission denied for id (804225045)
% 0.13/0.39  ipcrm: permission denied for id (804290582)
% 0.13/0.39  ipcrm: permission denied for id (804323351)
% 0.13/0.39  ipcrm: permission denied for id (804356120)
% 0.13/0.39  ipcrm: permission denied for id (804454427)
% 0.13/0.39  ipcrm: permission denied for id (804487196)
% 0.13/0.40  ipcrm: permission denied for id (804552735)
% 0.13/0.40  ipcrm: permission denied for id (804585505)
% 0.13/0.41  ipcrm: permission denied for id (804749350)
% 0.21/0.41  ipcrm: permission denied for id (804880426)
% 0.21/0.41  ipcrm: permission denied for id (804945964)
% 0.21/0.41  ipcrm: permission denied for id (804978733)
% 0.21/0.42  ipcrm: permission denied for id (805011502)
% 0.21/0.42  ipcrm: permission denied for id (805044271)
% 0.21/0.42  ipcrm: permission denied for id (805208117)
% 0.21/0.43  ipcrm: permission denied for id (805306425)
% 0.21/0.43  ipcrm: permission denied for id (805404732)
% 0.21/0.44  ipcrm: permission denied for id (805535810)
% 0.21/0.45  ipcrm: permission denied for id (805666888)
% 0.21/0.45  ipcrm: permission denied for id (805699657)
% 0.21/0.45  ipcrm: permission denied for id (805765195)
% 0.21/0.45  ipcrm: permission denied for id (805797964)
% 0.21/0.45  ipcrm: permission denied for id (805830733)
% 0.21/0.45  ipcrm: permission denied for id (805863503)
% 0.21/0.46  ipcrm: permission denied for id (805896272)
% 0.21/0.46  ipcrm: permission denied for id (805929041)
% 0.21/0.46  ipcrm: permission denied for id (805994581)
% 0.21/0.46  ipcrm: permission denied for id (806027351)
% 0.21/0.47  ipcrm: permission denied for id (806092889)
% 0.21/0.47  ipcrm: permission denied for id (806191198)
% 0.21/0.47  ipcrm: permission denied for id (806223967)
% 0.21/0.48  ipcrm: permission denied for id (806289506)
% 0.21/0.48  ipcrm: permission denied for id (806355045)
% 0.21/0.49  ipcrm: permission denied for id (806453355)
% 0.21/0.50  ipcrm: permission denied for id (806617203)
% 0.21/0.50  ipcrm: permission denied for id (806682743)
% 0.21/0.50  ipcrm: permission denied for id (806748280)
% 0.21/0.50  ipcrm: permission denied for id (806781049)
% 0.21/0.51  ipcrm: permission denied for id (806846590)
% 0.21/0.57  % (31030)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.57  % (31027)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.57  % (31029)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.57  % (31027)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    k1_wellord1(sK1,sK0) != k1_wellord1(sK1,sK0)),
% 0.21/0.57    inference(superposition,[],[f14,f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X0] : (k1_wellord1(sK1,X0) = k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0)))) )),
% 0.21/0.57    inference(global_subsumption,[],[f12,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ( ! [X0] : (k1_wellord1(sK1,X0) = k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0))) | ~v1_relat_1(sK1)) )),
% 0.21/0.57    inference(resolution,[],[f18,f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    v2_wellord1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) & v2_wellord1(sK1) & v1_relat_1(sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ? [X0,X1] : (k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) & v2_wellord1(X1) & v1_relat_1(X1)) => (k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) & v2_wellord1(sK1) & v1_relat_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f6,plain,(
% 0.21/0.57    ? [X0,X1] : (k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) & v2_wellord1(X1) & v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f5])).
% 0.21/0.57  fof(f5,plain,(
% 0.21/0.57    ? [X0,X1] : ((k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) & v2_wellord1(X1)) & v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f3])).
% 0.21/0.57  fof(f3,conjecture,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v2_wellord1(X0) | k1_wellord1(X0,X1) = k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_wellord1(X0,X1) = k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v2_wellord1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(resolution,[],[f16,f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k3_relat_1(X1)) | k3_relat_1(k2_wellord1(X1,X0)) = X0 | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ! [X0,X1] : (k3_relat_1(k2_wellord1(X1,X0)) = X0 | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f8])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ! [X0,X1] : ((k3_relat_1(k2_wellord1(X1,X0)) = X0 | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => k3_relat_1(k2_wellord1(X1,X0)) = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_wellord1)).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (31027)------------------------------
% 0.21/0.57  % (31027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (31027)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (31027)Memory used [KB]: 6012
% 0.21/0.57  % (31027)Time elapsed: 0.004 s
% 0.21/0.57  % (31027)------------------------------
% 0.21/0.57  % (31027)------------------------------
% 0.21/0.57  % (30887)Success in time 0.217 s
%------------------------------------------------------------------------------
