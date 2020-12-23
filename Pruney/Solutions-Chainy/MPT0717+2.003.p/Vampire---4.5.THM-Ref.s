%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  43 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 163 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f16,f14,f12,f25,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f25,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f13,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f13,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f23,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f14,f15,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f15,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,plain,(
    r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (25640)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (25645)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.47  % (25651)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % (25651)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f16,f14,f12,f25,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f23,f13,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK1,sK2),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & (v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f14,f15,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    v5_relat_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    r2_hidden(sK2,k1_relat_1(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (25651)------------------------------
% 0.22/0.48  % (25651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (25651)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (25651)Memory used [KB]: 895
% 0.22/0.48  % (25651)Time elapsed: 0.007 s
% 0.22/0.48  % (25651)------------------------------
% 0.22/0.48  % (25651)------------------------------
% 0.22/0.48  % (25643)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.48  % (25635)Success in time 0.116 s
%------------------------------------------------------------------------------
