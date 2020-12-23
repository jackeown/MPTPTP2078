%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 111 expanded)
%              Number of leaves         :    6 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 898 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f17,f19,f20,f21,f40,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | v5_ordinal1(k7_relat_1(X0,X1))
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v5_ordinal1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).

fof(f40,plain,(
    ~ v5_ordinal1(k7_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0] : v5_relat_1(k7_relat_1(sK1,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f18,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X2,X1)
      | v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

fof(f18,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
      | ~ v1_funct_1(k7_relat_1(sK1,sK2))
      | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
      | ~ v1_relat_1(k7_relat_1(sK1,sK2)) )
    & v3_ordinal1(sK2)
    & v5_ordinal1(sK1)
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
              | ~ v1_funct_1(k7_relat_1(X1,X2))
              | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
              | ~ v1_relat_1(k7_relat_1(X1,X2)) )
            & v3_ordinal1(X2) )
        & v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(sK1,X2))
            | ~ v1_funct_1(k7_relat_1(sK1,X2))
            | ~ v5_relat_1(k7_relat_1(sK1,X2),sK0)
            | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(sK1)
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ( ~ v5_ordinal1(k7_relat_1(sK1,X2))
          | ~ v1_funct_1(k7_relat_1(sK1,X2))
          | ~ v5_relat_1(k7_relat_1(sK1,X2),sK0)
          | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
        & v3_ordinal1(X2) )
   => ( ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
        | ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK2)) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( v5_ordinal1(k7_relat_1(X1,X2))
              & v1_funct_1(k7_relat_1(X1,X2))
              & v5_relat_1(k7_relat_1(X1,X2),X0)
              & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( v5_ordinal1(k7_relat_1(X1,X2))
            & v1_funct_1(k7_relat_1(X1,X2))
            & v5_relat_1(k7_relat_1(X1,X2),X0)
            & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).

fof(f33,plain,
    ( ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ v5_ordinal1(k7_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f17,f19,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f31,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f22,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f17,f19,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    v5_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (28688)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (28686)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % (28694)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (28694)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f19,f20,f21,f40,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v3_ordinal1(X1) | v5_ordinal1(k7_relat_1(X0,X1)) | ~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : ((v5_ordinal1(k7_relat_1(X0,X1)) & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v3_ordinal1(X1) | ~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : ((v5_ordinal1(k7_relat_1(X0,X1)) & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v3_ordinal1(X1) | ~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v5_ordinal1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v5_ordinal1(k7_relat_1(X0,X1)) & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ~v5_ordinal1(k7_relat_1(sK1,sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f33,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (v5_relat_1(k7_relat_1(sK1,X0),sK0)) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f18,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v5_relat_1(X2,X1) | v5_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    v5_relat_1(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ((~v5_ordinal1(k7_relat_1(sK1,sK2)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v5_relat_1(k7_relat_1(sK1,sK2),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK2))) & v3_ordinal1(sK2)) & v5_ordinal1(sK1) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f15,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(k7_relat_1(X1,X2)) | ~v1_funct_1(k7_relat_1(X1,X2)) | ~v5_relat_1(k7_relat_1(X1,X2),X0) | ~v1_relat_1(k7_relat_1(X1,X2))) & v3_ordinal1(X2)) & v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (? [X2] : ((~v5_ordinal1(k7_relat_1(sK1,X2)) | ~v1_funct_1(k7_relat_1(sK1,X2)) | ~v5_relat_1(k7_relat_1(sK1,X2),sK0) | ~v1_relat_1(k7_relat_1(sK1,X2))) & v3_ordinal1(X2)) & v5_ordinal1(sK1) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X2] : ((~v5_ordinal1(k7_relat_1(sK1,X2)) | ~v1_funct_1(k7_relat_1(sK1,X2)) | ~v5_relat_1(k7_relat_1(sK1,X2),sK0) | ~v1_relat_1(k7_relat_1(sK1,X2))) & v3_ordinal1(X2)) => ((~v5_ordinal1(k7_relat_1(sK1,sK2)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v5_relat_1(k7_relat_1(sK1,sK2),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK2))) & v3_ordinal1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(k7_relat_1(X1,X2)) | ~v1_funct_1(k7_relat_1(X1,X2)) | ~v5_relat_1(k7_relat_1(X1,X2),X0) | ~v1_relat_1(k7_relat_1(X1,X2))) & v3_ordinal1(X2)) & v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(k7_relat_1(X1,X2)) | ~v1_funct_1(k7_relat_1(X1,X2)) | ~v5_relat_1(k7_relat_1(X1,X2),X0) | ~v1_relat_1(k7_relat_1(X1,X2))) & v3_ordinal1(X2)) & (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : ((v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (v3_ordinal1(X2) => (v5_ordinal1(k7_relat_1(X1,X2)) & v1_funct_1(k7_relat_1(X1,X2)) & v5_relat_1(k7_relat_1(X1,X2),X0) & v1_relat_1(k7_relat_1(X1,X2)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0,X1] : ((v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (v3_ordinal1(X2) => (v5_ordinal1(k7_relat_1(X1,X2)) & v1_funct_1(k7_relat_1(X1,X2)) & v5_relat_1(k7_relat_1(X1,X2),X0) & v1_relat_1(k7_relat_1(X1,X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ~v5_relat_1(k7_relat_1(sK1,sK2),sK0) | ~v5_ordinal1(k7_relat_1(sK1,sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f31,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_1(k7_relat_1(sK1,X0))) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f19,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~v5_ordinal1(k7_relat_1(sK1,sK2)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v5_relat_1(k7_relat_1(sK1,sK2),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f22,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f19,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ~v5_ordinal1(k7_relat_1(sK1,sK2)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v5_relat_1(k7_relat_1(sK1,sK2),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    v3_ordinal1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v5_ordinal1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    v1_funct_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (28694)------------------------------
% 0.20/0.47  % (28694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (28694)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (28694)Memory used [KB]: 5373
% 0.20/0.47  % (28694)Time elapsed: 0.064 s
% 0.20/0.47  % (28694)------------------------------
% 0.20/0.47  % (28694)------------------------------
% 0.20/0.48  % (28679)Success in time 0.117 s
%------------------------------------------------------------------------------
