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
% DateTime   : Thu Dec  3 12:49:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 114 expanded)
%              Number of leaves         :    4 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 417 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f12,f27,f32,f34,f36,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f36,plain,(
    r2_hidden(k4_tarski(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),sK3) ),
    inference(unit_resulting_resolution,[],[f13,f35,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f35,plain,(
    r2_hidden(k4_tarski(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),sK2) ),
    inference(unit_resulting_resolution,[],[f16,f26,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    r2_hidden(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f15,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f29,f33,f19])).

fof(f33,plain,(
    r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f16,f26,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f16,f13,f12,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f32,plain,(
    r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f14,f31,f19])).

fof(f31,plain,(
    r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f16,f26,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,(
    ~ r2_hidden(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),k9_relat_1(sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f15,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (24621)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.47  % (24633)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (24635)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (24635)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f12,f27,f32,f34,f36,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),sK3)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f13,f35,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f16,f26,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r2_hidden(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),k9_relat_1(sK2,sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f15,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    r1_tarski(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),k1_relat_1(sK3))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f29,f33,f19])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),k1_relat_1(sK2))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f16,f26,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f16,f13,f12,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),sK1)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f14,f31,f19])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),sK0,sK2),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f16,f26,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ~r2_hidden(sK4(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)),k9_relat_1(sK3,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f15,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    v1_relat_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (24635)------------------------------
% 0.21/0.48  % (24635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24635)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (24635)Memory used [KB]: 895
% 0.21/0.48  % (24635)Time elapsed: 0.004 s
% 0.21/0.48  % (24635)------------------------------
% 0.21/0.48  % (24635)------------------------------
% 0.21/0.48  % (24630)WARNING: option uwaf not known.
% 0.21/0.48  % (24617)Success in time 0.126 s
%------------------------------------------------------------------------------
