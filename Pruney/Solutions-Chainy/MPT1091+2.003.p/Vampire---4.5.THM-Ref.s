%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 220 expanded)
%              Number of leaves         :    7 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  118 ( 591 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(global_subsumption,[],[f18,f40,f52,f108])).

fof(f108,plain,(
    v1_finset_1(sK1) ),
    inference(subsumption_resolution,[],[f107,f52])).

fof(f107,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK1) ),
    inference(resolution,[],[f106,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(f106,plain,(
    r1_tarski(sK1,k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( r1_tarski(sK1,k3_tarski(sK0))
    | r1_tarski(sK1,k3_tarski(sK0)) ),
    inference(resolution,[],[f88,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f88,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3(X4,k3_tarski(sK0)),sK1)
      | r1_tarski(X4,k3_tarski(sK0)) ) ),
    inference(resolution,[],[f84,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X14] :
      ( r2_hidden(X14,k3_tarski(sK0))
      | ~ r2_hidden(X14,sK1) ) ),
    inference(resolution,[],[f34,f55])).

fof(f55,plain,(
    r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f40,f17])).

fof(f17,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_finset_1(k3_tarski(sK0))
    | r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f52,plain,(
    v1_finset_1(k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f51,f40])).

fof(f51,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0)
    | v1_finset_1(k3_tarski(sK0)) ),
    inference(resolution,[],[f49,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_finset_1(sK2(X0))
      | ~ v1_finset_1(X0)
      | v1_finset_1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(f49,plain,
    ( v1_finset_1(sK2(sK0))
    | v1_finset_1(k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f48,f40])).

fof(f48,plain,
    ( ~ v1_finset_1(sK0)
    | v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK2(sK0)) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,
    ( ~ v1_finset_1(sK0)
    | v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK2(sK0)) ),
    inference(resolution,[],[f22,f16])).

fof(f16,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v1_finset_1(k3_tarski(sK0))
      | v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | ~ v1_finset_1(X0)
      | v1_finset_1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    v1_finset_1(sK0) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,
    ( v1_finset_1(sK0)
    | v1_finset_1(sK0) ),
    inference(resolution,[],[f38,f19])).

fof(f19,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k3_tarski(X0))
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k1_zfmisc_1(k3_tarski(X0)))
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f24,f20])).

fof(f20,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f18,plain,
    ( ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0)
    | ~ v1_finset_1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (2322)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (2345)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (2322)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(global_subsumption,[],[f18,f40,f52,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    v1_finset_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f107,f52])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ~v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f106,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    r1_tarski(sK1,k3_tarski(sK0))),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    r1_tarski(sK1,k3_tarski(sK0)) | r1_tarski(sK1,k3_tarski(sK0))),
% 0.21/0.53    inference(resolution,[],[f88,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(sK3(X4,k3_tarski(sK0)),sK1) | r1_tarski(X4,k3_tarski(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f84,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X14] : (r2_hidden(X14,k3_tarski(sK0)) | ~r2_hidden(X14,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f34,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f52,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ~v1_finset_1(k3_tarski(sK0)) | r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f40,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ~v1_finset_1(sK0) | ~v1_finset_1(k3_tarski(sK0)) | r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) <~> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3) | r2_hidden(X2,k3_tarski(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    v1_finset_1(k3_tarski(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f51,f40])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0) | v1_finset_1(k3_tarski(sK0))),
% 0.21/0.53    inference(resolution,[],[f49,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_finset_1(sK2(X0)) | ~v1_finset_1(X0) | v1_finset_1(k3_tarski(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) => v1_finset_1(k3_tarski(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    v1_finset_1(sK2(sK0)) | v1_finset_1(k3_tarski(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f48,f40])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~v1_finset_1(sK0) | v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK2(sK0))),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ~v1_finset_1(sK0) | v1_finset_1(k3_tarski(sK0)) | v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK2(sK0))),
% 0.21/0.53    inference(resolution,[],[f22,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK0) | v1_finset_1(k3_tarski(sK0)) | v1_finset_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | ~v1_finset_1(X0) | v1_finset_1(k3_tarski(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    v1_finset_1(sK0)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v1_finset_1(sK0) | v1_finset_1(sK0)),
% 0.21/0.53    inference(resolution,[],[f38,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_finset_1(k3_tarski(X0)) | v1_finset_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f37,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v1_finset_1(X0) => v1_finset_1(k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_finset_1(k1_zfmisc_1(k3_tarski(X0))) | v1_finset_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f24,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ~v1_finset_1(sK1) | ~v1_finset_1(sK0) | ~v1_finset_1(k3_tarski(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2322)------------------------------
% 0.21/0.53  % (2322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2322)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2322)Memory used [KB]: 6268
% 0.21/0.53  % (2322)Time elapsed: 0.112 s
% 0.21/0.53  % (2322)------------------------------
% 0.21/0.53  % (2322)------------------------------
% 0.21/0.53  % (2309)Success in time 0.175 s
%------------------------------------------------------------------------------
