%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:27 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   30 (  50 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 131 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f29])).

fof(f29,plain,(
    ! [X6] : r1_tarski(k8_relat_1(X6,sK2),sK2) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).

fof(f38,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X7] : v1_relat_1(k8_relat_1(X7,sK2)) ),
    inference(resolution,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f37,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f36,f17])).

fof(f36,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f35,f26])).

fof(f26,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f35,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f18,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f18,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:06:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (818446336)
% 0.14/0.37  ipcrm: permission denied for id (818479105)
% 0.14/0.37  ipcrm: permission denied for id (818511877)
% 0.14/0.38  ipcrm: permission denied for id (818544648)
% 0.14/0.38  ipcrm: permission denied for id (818577420)
% 0.14/0.39  ipcrm: permission denied for id (818642959)
% 0.14/0.40  ipcrm: permission denied for id (818774040)
% 0.14/0.40  ipcrm: permission denied for id (818839578)
% 0.14/0.40  ipcrm: permission denied for id (818905116)
% 0.20/0.41  ipcrm: permission denied for id (819003423)
% 0.20/0.41  ipcrm: permission denied for id (819036192)
% 0.20/0.41  ipcrm: permission denied for id (819068962)
% 0.20/0.41  ipcrm: permission denied for id (819101733)
% 0.20/0.42  ipcrm: permission denied for id (819200043)
% 0.20/0.42  ipcrm: permission denied for id (819232812)
% 0.20/0.43  ipcrm: permission denied for id (819298351)
% 0.20/0.43  ipcrm: permission denied for id (819363892)
% 0.20/0.44  ipcrm: permission denied for id (819462202)
% 0.20/0.44  ipcrm: permission denied for id (819494972)
% 0.20/0.46  ipcrm: permission denied for id (819822667)
% 0.20/0.47  ipcrm: permission denied for id (819888209)
% 0.20/0.48  ipcrm: permission denied for id (820019287)
% 0.20/0.48  ipcrm: permission denied for id (820117597)
% 0.20/0.49  ipcrm: permission denied for id (820183135)
% 0.20/0.49  ipcrm: permission denied for id (820314212)
% 0.20/0.50  ipcrm: permission denied for id (820445292)
% 0.20/0.50  ipcrm: permission denied for id (820510831)
% 0.20/0.51  ipcrm: permission denied for id (820576373)
% 0.20/0.52  ipcrm: permission denied for id (820707449)
% 0.81/0.63  % (24283)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.05/0.63  % (24283)Refutation found. Thanks to Tanya!
% 1.05/0.63  % SZS status Theorem for theBenchmark
% 1.05/0.63  % SZS output start Proof for theBenchmark
% 1.05/0.63  fof(f45,plain,(
% 1.05/0.63    $false),
% 1.05/0.63    inference(subsumption_resolution,[],[f38,f29])).
% 1.05/0.63  fof(f29,plain,(
% 1.05/0.63    ( ! [X6] : (r1_tarski(k8_relat_1(X6,sK2),sK2)) )),
% 1.05/0.63    inference(resolution,[],[f17,f20])).
% 1.05/0.63  fof(f20,plain,(
% 1.05/0.63    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 1.05/0.63    inference(cnf_transformation,[],[f10])).
% 1.05/0.63  fof(f10,plain,(
% 1.05/0.63    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 1.05/0.63    inference(ennf_transformation,[],[f3])).
% 1.05/0.63  fof(f3,axiom,(
% 1.05/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 1.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 1.05/0.63  fof(f17,plain,(
% 1.05/0.63    v1_relat_1(sK2)),
% 1.05/0.63    inference(cnf_transformation,[],[f14])).
% 1.05/0.63  fof(f14,plain,(
% 1.05/0.63    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 1.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 1.05/0.63  fof(f13,plain,(
% 1.05/0.63    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 1.05/0.63    introduced(choice_axiom,[])).
% 1.05/0.63  fof(f8,plain,(
% 1.05/0.63    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 1.05/0.63    inference(ennf_transformation,[],[f7])).
% 1.05/0.63  fof(f7,plain,(
% 1.05/0.63    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 1.05/0.63    inference(pure_predicate_removal,[],[f6])).
% 1.05/0.63  fof(f6,negated_conjecture,(
% 1.05/0.63    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 1.05/0.63    inference(negated_conjecture,[],[f5])).
% 1.05/0.63  fof(f5,conjecture,(
% 1.05/0.63    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 1.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).
% 1.05/0.63  fof(f38,plain,(
% 1.05/0.63    ~r1_tarski(k8_relat_1(sK0,sK2),sK2)),
% 1.05/0.63    inference(subsumption_resolution,[],[f37,f30])).
% 1.05/0.63  fof(f30,plain,(
% 1.05/0.63    ( ! [X7] : (v1_relat_1(k8_relat_1(X7,sK2))) )),
% 1.05/0.63    inference(resolution,[],[f17,f19])).
% 1.05/0.63  fof(f19,plain,(
% 1.05/0.63    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.05/0.63    inference(cnf_transformation,[],[f9])).
% 1.05/0.63  fof(f9,plain,(
% 1.05/0.63    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.05/0.63    inference(ennf_transformation,[],[f2])).
% 1.05/0.63  fof(f2,axiom,(
% 1.05/0.63    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.05/0.63  fof(f37,plain,(
% 1.05/0.63    ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.05/0.63    inference(subsumption_resolution,[],[f36,f17])).
% 1.05/0.63  fof(f36,plain,(
% 1.05/0.63    ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.05/0.63    inference(subsumption_resolution,[],[f35,f26])).
% 1.05/0.63  fof(f26,plain,(
% 1.05/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.05/0.63    inference(equality_resolution,[],[f21])).
% 1.05/0.63  fof(f21,plain,(
% 1.05/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.05/0.63    inference(cnf_transformation,[],[f16])).
% 1.05/0.63  fof(f16,plain,(
% 1.05/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.05/0.63    inference(flattening,[],[f15])).
% 1.05/0.63  fof(f15,plain,(
% 1.05/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.05/0.63    inference(nnf_transformation,[],[f1])).
% 1.05/0.63  fof(f1,axiom,(
% 1.05/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.05/0.63  fof(f35,plain,(
% 1.05/0.63    ~r1_tarski(sK1,sK1) | ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.05/0.63    inference(resolution,[],[f18,f24])).
% 1.05/0.63  fof(f24,plain,(
% 1.05/0.63    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.05/0.63    inference(cnf_transformation,[],[f12])).
% 1.05/0.63  fof(f12,plain,(
% 1.05/0.63    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.05/0.63    inference(flattening,[],[f11])).
% 1.05/0.63  fof(f11,plain,(
% 1.05/0.63    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.05/0.63    inference(ennf_transformation,[],[f4])).
% 1.05/0.63  fof(f4,axiom,(
% 1.05/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 1.05/0.63  fof(f18,plain,(
% 1.05/0.63    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),
% 1.05/0.63    inference(cnf_transformation,[],[f14])).
% 1.05/0.63  % SZS output end Proof for theBenchmark
% 1.05/0.63  % (24283)------------------------------
% 1.05/0.63  % (24283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.05/0.63  % (24283)Termination reason: Refutation
% 1.05/0.63  
% 1.05/0.63  % (24283)Memory used [KB]: 1535
% 1.05/0.63  % (24283)Time elapsed: 0.047 s
% 1.05/0.63  % (24283)------------------------------
% 1.05/0.63  % (24283)------------------------------
% 1.05/0.64  % (24131)Success in time 0.275 s
%------------------------------------------------------------------------------
