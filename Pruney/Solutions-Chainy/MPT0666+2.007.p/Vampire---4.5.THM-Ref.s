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
% DateTime   : Thu Dec  3 12:53:20 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   21 (  43 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 147 expanded)
%              Number of equality atoms :   24 (  64 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(global_subsumption,[],[f12,f28,f31])).

fof(f31,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(resolution,[],[f30,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_funct_1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,sK0) = k7_relat_1(k7_relat_1(X0,sK1),sK0) ) ),
    inference(resolution,[],[f16,f14])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f28,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f27,f13])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,sK0) = k7_relat_1(k7_relat_1(X0,sK0),sK1) ) ),
    inference(resolution,[],[f15,f14])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f12,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:53:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.40  % (22826)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.12/0.41  % (22819)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.12/0.41  % (22819)Refutation found. Thanks to Tanya!
% 0.12/0.41  % SZS status Theorem for theBenchmark
% 0.12/0.41  % SZS output start Proof for theBenchmark
% 0.12/0.41  fof(f34,plain,(
% 0.12/0.41    $false),
% 0.12/0.41    inference(global_subsumption,[],[f12,f28,f31])).
% 0.12/0.41  fof(f31,plain,(
% 0.12/0.41    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.12/0.41    inference(resolution,[],[f30,f13])).
% 0.12/0.41  fof(f13,plain,(
% 0.12/0.41    v1_relat_1(sK2)),
% 0.12/0.41    inference(cnf_transformation,[],[f7])).
% 0.12/0.41  fof(f7,plain,(
% 0.12/0.41    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.12/0.41    inference(flattening,[],[f6])).
% 0.12/0.41  fof(f6,plain,(
% 0.12/0.41    ? [X0,X1,X2] : (((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.12/0.41    inference(ennf_transformation,[],[f5])).
% 0.12/0.41  fof(f5,plain,(
% 0.12/0.41    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.12/0.41    inference(pure_predicate_removal,[],[f4])).
% 0.12/0.41  fof(f4,negated_conjecture,(
% 0.12/0.41    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.12/0.41    inference(negated_conjecture,[],[f3])).
% 0.12/0.41  fof(f3,conjecture,(
% 0.12/0.41    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_funct_1)).
% 0.12/0.41  fof(f30,plain,(
% 0.12/0.41    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,sK0) = k7_relat_1(k7_relat_1(X0,sK1),sK0)) )),
% 0.12/0.41    inference(resolution,[],[f16,f14])).
% 0.12/0.41  fof(f14,plain,(
% 0.12/0.41    r1_tarski(sK0,sK1)),
% 0.12/0.41    inference(cnf_transformation,[],[f7])).
% 0.12/0.41  fof(f16,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f11])).
% 0.12/0.41  fof(f11,plain,(
% 0.12/0.41    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.12/0.41    inference(flattening,[],[f10])).
% 0.12/0.41  fof(f10,plain,(
% 0.12/0.41    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.12/0.41    inference(ennf_transformation,[],[f2])).
% 0.12/0.41  fof(f2,axiom,(
% 0.12/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.12/0.41  fof(f28,plain,(
% 0.12/0.41    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.12/0.41    inference(resolution,[],[f27,f13])).
% 0.12/0.41  fof(f27,plain,(
% 0.12/0.41    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,sK0) = k7_relat_1(k7_relat_1(X0,sK0),sK1)) )),
% 0.12/0.41    inference(resolution,[],[f15,f14])).
% 0.12/0.41  fof(f15,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f9])).
% 0.12/0.41  fof(f9,plain,(
% 0.12/0.41    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.12/0.41    inference(flattening,[],[f8])).
% 0.12/0.41  fof(f8,plain,(
% 0.12/0.41    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.12/0.41    inference(ennf_transformation,[],[f1])).
% 0.12/0.41  fof(f1,axiom,(
% 0.12/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.12/0.41  fof(f12,plain,(
% 0.12/0.41    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.12/0.41    inference(cnf_transformation,[],[f7])).
% 0.12/0.41  % SZS output end Proof for theBenchmark
% 0.12/0.41  % (22819)------------------------------
% 0.12/0.41  % (22819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.41  % (22819)Termination reason: Refutation
% 0.12/0.41  
% 0.12/0.41  % (22819)Memory used [KB]: 10490
% 0.12/0.41  % (22819)Time elapsed: 0.005 s
% 0.12/0.41  % (22819)------------------------------
% 0.12/0.41  % (22819)------------------------------
% 0.12/0.41  % (22818)Success in time 0.061 s
%------------------------------------------------------------------------------
