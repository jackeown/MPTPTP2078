%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   14 (  26 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  82 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f10,f12,f11,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v3_relat_1(X0)
      | v3_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_relat_1(X0)
        & v1_relat_1(X0) )
     => ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc19_relat_1)).

fof(f11,plain,(
    ~ v3_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( v3_relat_1(sK1)
    & ~ v3_relat_1(k7_relat_1(sK1,sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( v3_relat_1(X1)
        & ~ v3_relat_1(k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( v3_relat_1(sK1)
      & ~ v3_relat_1(k7_relat_1(sK1,sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( v3_relat_1(X1)
      & ~ v3_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( v3_relat_1(X1)
      & ~ v3_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( v3_relat_1(X1)
            & ~ v3_relat_1(k7_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( v3_relat_1(X1)
          & ~ v3_relat_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_relat_1)).

fof(f12,plain,(
    v3_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (32011)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.44  % (32004)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.44  % (32011)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f10,f12,f11,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v3_relat_1(X0) | v3_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0,X1] : ((v3_relat_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v3_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ! [X0,X1] : ((v3_relat_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v3_relat_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v3_relat_1(X0) & v1_relat_1(X0)) => (v3_relat_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc19_relat_1)).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ~v3_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    v3_relat_1(sK1) & ~v3_relat_1(k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1] : (v3_relat_1(X1) & ~v3_relat_1(k7_relat_1(X1,X0)) & v1_relat_1(X1)) => (v3_relat_1(sK1) & ~v3_relat_1(k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f5,plain,(
% 0.21/0.44    ? [X0,X1] : (v3_relat_1(X1) & ~v3_relat_1(k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f4])).
% 0.21/0.44  fof(f4,plain,(
% 0.21/0.44    ? [X0,X1] : ((v3_relat_1(X1) & ~v3_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => ~(v3_relat_1(X1) & ~v3_relat_1(k7_relat_1(X1,X0))))),
% 0.21/0.44    inference(negated_conjecture,[],[f2])).
% 0.21/0.44  fof(f2,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => ~(v3_relat_1(X1) & ~v3_relat_1(k7_relat_1(X1,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_relat_1)).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    v3_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (32011)------------------------------
% 0.21/0.44  % (32011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (32011)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (32011)Memory used [KB]: 5245
% 0.21/0.44  % (32011)Time elapsed: 0.051 s
% 0.21/0.44  % (32011)------------------------------
% 0.21/0.44  % (32011)------------------------------
% 0.21/0.44  % (31996)Success in time 0.091 s
%------------------------------------------------------------------------------
