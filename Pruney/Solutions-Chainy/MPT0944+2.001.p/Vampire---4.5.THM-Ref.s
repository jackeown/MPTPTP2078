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
% DateTime   : Thu Dec  3 12:59:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  38 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 100 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f17])).

fof(f17,plain,(
    ~ v2_wellord1(k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v2_wellord1(k1_wellord2(sK1))
    & r1_tarski(sK1,sK0)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(k1_wellord2(X1))
            & r1_tarski(X1,X0) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(k1_wellord2(X1))
          & r1_tarski(X1,sK0) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ~ v2_wellord1(k1_wellord2(X1))
        & r1_tarski(X1,sK0) )
   => ( ~ v2_wellord1(k1_wellord2(sK1))
      & r1_tarski(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(k1_wellord2(X1))
          & r1_tarski(X1,X0) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( r1_tarski(X1,X0)
           => v2_wellord1(k1_wellord2(X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord2)).

fof(f28,plain,(
    v2_wellord1(k1_wellord2(sK1)) ),
    inference(superposition,[],[f25,f26])).

fof(f26,plain,(
    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f16,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f16,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] : v2_wellord1(k2_wellord1(k1_wellord2(sK0),X0)) ),
    inference(unit_resulting_resolution,[],[f18,f22,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(f22,plain,(
    v2_wellord1(k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f15,f19])).

fof(f19,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f15,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 16:07:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.43  % (10131)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.44  % (10129)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.44  % (10131)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f28,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ~v2_wellord1(k1_wellord2(sK1))),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    (~v2_wellord1(k1_wellord2(sK1)) & r1_tarski(sK1,sK0)) & v3_ordinal1(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~v2_wellord1(k1_wellord2(X1)) & r1_tarski(X1,X0)) & v3_ordinal1(X0)) => (? [X1] : (~v2_wellord1(k1_wellord2(X1)) & r1_tarski(X1,sK0)) & v3_ordinal1(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X1] : (~v2_wellord1(k1_wellord2(X1)) & r1_tarski(X1,sK0)) => (~v2_wellord1(k1_wellord2(sK1)) & r1_tarski(sK1,sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~v2_wellord1(k1_wellord2(X1)) & r1_tarski(X1,X0)) & v3_ordinal1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (r1_tarski(X1,X0) => v2_wellord1(k1_wellord2(X1))))),
% 0.22/0.44    inference(negated_conjecture,[],[f5])).
% 0.22/0.44  fof(f5,conjecture,(
% 0.22/0.44    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (r1_tarski(X1,X0) => v2_wellord1(k1_wellord2(X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord2)).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    v2_wellord1(k1_wellord2(sK1))),
% 0.22/0.44    inference(superposition,[],[f25,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f16,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    r1_tarski(sK1,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0] : (v2_wellord1(k2_wellord1(k1_wellord2(sK0),X0))) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f18,f22,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : ((v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => v2_wellord1(k2_wellord1(X1,X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    v2_wellord1(k1_wellord2(sK0))),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f15,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    v3_ordinal1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (10131)------------------------------
% 0.22/0.44  % (10131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (10131)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (10131)Memory used [KB]: 6012
% 0.22/0.44  % (10131)Time elapsed: 0.004 s
% 0.22/0.44  % (10131)------------------------------
% 0.22/0.44  % (10131)------------------------------
% 0.22/0.44  % (10128)Success in time 0.07 s
%------------------------------------------------------------------------------
