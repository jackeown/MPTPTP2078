%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:22 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 137 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 456 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f33,f49,f53,f58,f62,f67])).

fof(f67,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f59,f20,f23])).

fof(f23,plain,
    ( spl3_2
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f20,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f21,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK2)))
      | r2_hidden(k1_funct_1(sK2,X0),X1) ) ),
    inference(forward_demodulation,[],[f39,f34])).

fof(f34,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    inference(resolution,[],[f15,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(sK2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f38,f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ) ),
    inference(resolution,[],[f17,f14])).

fof(f14,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(f21,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f62,plain,
    ( ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f57,f21])).

fof(f57,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X0] : ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f54,f27,f56])).

fof(f27,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2)))
    | spl3_3 ),
    inference(resolution,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK2))) ) ),
    inference(forward_demodulation,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f35,f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ) ),
    inference(resolution,[],[f16,f14])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f53,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f50,f24])).

fof(f24,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f50,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f48,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2)))
        | ~ r2_hidden(k1_funct_1(sK2,sK0),X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_4
  <=> ! [X0] :
        ( r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2)))
        | ~ r2_hidden(k1_funct_1(sK2,sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f49,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f27,f47])).

fof(f44,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2)))
        | ~ r2_hidden(k1_funct_1(sK2,sK0),X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f43,f28])).

fof(f28,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK2)))
      | ~ r2_hidden(k1_funct_1(sK2,X0),X1) ) ),
    inference(forward_demodulation,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,X0),X1)
      | r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f41,f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,X0),X1)
      | r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ) ),
    inference(resolution,[],[f18,f14])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f10,f27,f23,f20])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f11,f27,f20])).

fof(f11,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f12,f23,f20])).

fof(f12,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n003.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 15:08:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.39  % (24205)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.18/0.39  % (24206)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.18/0.40  % (24201)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.18/0.40  % (24201)Refutation found. Thanks to Tanya!
% 0.18/0.40  % SZS status Theorem for theBenchmark
% 0.18/0.40  % SZS output start Proof for theBenchmark
% 0.18/0.40  fof(f68,plain,(
% 0.18/0.40    $false),
% 0.18/0.40    inference(avatar_sat_refutation,[],[f25,f29,f33,f49,f53,f58,f62,f67])).
% 0.18/0.40  fof(f67,plain,(
% 0.18/0.40    spl3_2 | ~spl3_1),
% 0.18/0.40    inference(avatar_split_clause,[],[f59,f20,f23])).
% 0.18/0.40  fof(f23,plain,(
% 0.18/0.40    spl3_2 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.40  fof(f20,plain,(
% 0.18/0.40    spl3_1 <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.40  fof(f59,plain,(
% 0.18/0.40    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl3_1),
% 0.18/0.40    inference(resolution,[],[f21,f40])).
% 0.18/0.40  fof(f40,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK2))) | r2_hidden(k1_funct_1(sK2,X0),X1)) )),
% 0.18/0.40    inference(forward_demodulation,[],[f39,f34])).
% 0.18/0.40  fof(f34,plain,(
% 0.18/0.40    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 0.18/0.40    inference(resolution,[],[f15,f13])).
% 0.18/0.40  fof(f13,plain,(
% 0.18/0.40    v1_relat_1(sK2)),
% 0.18/0.40    inference(cnf_transformation,[],[f6])).
% 0.18/0.40  fof(f6,plain,(
% 0.18/0.40    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.18/0.40    inference(flattening,[],[f5])).
% 0.18/0.40  fof(f5,plain,(
% 0.18/0.40    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.18/0.40    inference(ennf_transformation,[],[f4])).
% 0.18/0.40  fof(f4,negated_conjecture,(
% 0.18/0.40    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.18/0.40    inference(negated_conjecture,[],[f3])).
% 0.18/0.40  fof(f3,conjecture,(
% 0.18/0.40    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).
% 0.18/0.40  fof(f15,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f7])).
% 0.18/0.40  fof(f7,plain,(
% 0.18/0.40    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.18/0.40    inference(ennf_transformation,[],[f1])).
% 0.18/0.40  fof(f1,axiom,(
% 0.18/0.40    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.18/0.40  fof(f39,plain,(
% 0.18/0.40    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(subsumption_resolution,[],[f38,f13])).
% 0.18/0.40  fof(f38,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(resolution,[],[f17,f14])).
% 0.18/0.40  fof(f14,plain,(
% 0.18/0.40    v1_funct_1(sK2)),
% 0.18/0.40    inference(cnf_transformation,[],[f6])).
% 0.18/0.40  fof(f17,plain,(
% 0.18/0.40    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f9])).
% 0.18/0.40  fof(f9,plain,(
% 0.18/0.40    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.18/0.40    inference(flattening,[],[f8])).
% 0.18/0.40  fof(f8,plain,(
% 0.18/0.40    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.18/0.40    inference(ennf_transformation,[],[f2])).
% 0.18/0.40  fof(f2,axiom,(
% 0.18/0.40    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).
% 0.18/0.40  fof(f21,plain,(
% 0.18/0.40    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | ~spl3_1),
% 0.18/0.40    inference(avatar_component_clause,[],[f20])).
% 0.18/0.40  fof(f62,plain,(
% 0.18/0.40    ~spl3_1 | ~spl3_5),
% 0.18/0.40    inference(avatar_contradiction_clause,[],[f61])).
% 0.18/0.40  fof(f61,plain,(
% 0.18/0.40    $false | (~spl3_1 | ~spl3_5)),
% 0.18/0.40    inference(resolution,[],[f57,f21])).
% 0.18/0.40  fof(f57,plain,(
% 0.18/0.40    ( ! [X0] : (~r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2)))) ) | ~spl3_5),
% 0.18/0.40    inference(avatar_component_clause,[],[f56])).
% 0.18/0.40  fof(f56,plain,(
% 0.18/0.40    spl3_5 <=> ! [X0] : ~r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2)))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.18/0.40  fof(f58,plain,(
% 0.18/0.40    spl3_5 | spl3_3),
% 0.18/0.40    inference(avatar_split_clause,[],[f54,f27,f56])).
% 0.18/0.40  fof(f27,plain,(
% 0.18/0.40    spl3_3 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.40  fof(f54,plain,(
% 0.18/0.40    ( ! [X0] : (~r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2)))) ) | spl3_3),
% 0.18/0.40    inference(resolution,[],[f32,f37])).
% 0.18/0.40  fof(f37,plain,(
% 0.18/0.40    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK2)))) )),
% 0.18/0.40    inference(forward_demodulation,[],[f36,f34])).
% 0.18/0.40  fof(f36,plain,(
% 0.18/0.40    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(subsumption_resolution,[],[f35,f13])).
% 0.18/0.40  fof(f35,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~v1_relat_1(sK2) | r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(resolution,[],[f16,f14])).
% 0.18/0.40  fof(f16,plain,(
% 0.18/0.40    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f9])).
% 0.18/0.40  fof(f32,plain,(
% 0.18/0.40    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl3_3),
% 0.18/0.40    inference(avatar_component_clause,[],[f27])).
% 0.18/0.40  fof(f53,plain,(
% 0.18/0.40    spl3_1 | ~spl3_2 | ~spl3_4),
% 0.18/0.40    inference(avatar_contradiction_clause,[],[f52])).
% 0.18/0.40  fof(f52,plain,(
% 0.18/0.40    $false | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.18/0.40    inference(subsumption_resolution,[],[f50,f24])).
% 0.18/0.40  fof(f24,plain,(
% 0.18/0.40    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl3_2),
% 0.18/0.40    inference(avatar_component_clause,[],[f23])).
% 0.18/0.40  fof(f50,plain,(
% 0.18/0.40    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | (spl3_1 | ~spl3_4)),
% 0.18/0.40    inference(resolution,[],[f48,f30])).
% 0.18/0.40  fof(f30,plain,(
% 0.18/0.40    ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | spl3_1),
% 0.18/0.40    inference(avatar_component_clause,[],[f20])).
% 0.18/0.40  fof(f48,plain,(
% 0.18/0.40    ( ! [X0] : (r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2))) | ~r2_hidden(k1_funct_1(sK2,sK0),X0)) ) | ~spl3_4),
% 0.18/0.40    inference(avatar_component_clause,[],[f47])).
% 0.18/0.40  fof(f47,plain,(
% 0.18/0.40    spl3_4 <=> ! [X0] : (r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2))) | ~r2_hidden(k1_funct_1(sK2,sK0),X0))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.18/0.40  fof(f49,plain,(
% 0.18/0.40    spl3_4 | ~spl3_3),
% 0.18/0.40    inference(avatar_split_clause,[],[f44,f27,f47])).
% 0.18/0.40  fof(f44,plain,(
% 0.18/0.40    ( ! [X0] : (r2_hidden(sK0,k1_relat_1(k8_relat_1(X0,sK2))) | ~r2_hidden(k1_funct_1(sK2,sK0),X0)) ) | ~spl3_3),
% 0.18/0.40    inference(resolution,[],[f43,f28])).
% 0.18/0.40  fof(f28,plain,(
% 0.18/0.40    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl3_3),
% 0.18/0.40    inference(avatar_component_clause,[],[f27])).
% 0.18/0.40  fof(f43,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK2))) | ~r2_hidden(k1_funct_1(sK2,X0),X1)) )),
% 0.18/0.40    inference(forward_demodulation,[],[f42,f34])).
% 0.18/0.40  fof(f42,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X0),X1) | r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(subsumption_resolution,[],[f41,f13])).
% 0.18/0.40  fof(f41,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X0),X1) | r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(resolution,[],[f18,f14])).
% 0.18/0.40  fof(f18,plain,(
% 0.18/0.40    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k1_funct_1(X2,X0),X1) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f9])).
% 0.18/0.40  fof(f33,plain,(
% 0.18/0.40    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.18/0.40    inference(avatar_split_clause,[],[f10,f27,f23,f20])).
% 0.18/0.40  fof(f10,plain,(
% 0.18/0.40    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.18/0.40    inference(cnf_transformation,[],[f6])).
% 0.18/0.40  fof(f29,plain,(
% 0.18/0.40    spl3_1 | spl3_3),
% 0.18/0.40    inference(avatar_split_clause,[],[f11,f27,f20])).
% 0.18/0.40  fof(f11,plain,(
% 0.18/0.40    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.18/0.40    inference(cnf_transformation,[],[f6])).
% 0.18/0.40  fof(f25,plain,(
% 0.18/0.40    spl3_1 | spl3_2),
% 0.18/0.40    inference(avatar_split_clause,[],[f12,f23,f20])).
% 0.18/0.40  fof(f12,plain,(
% 0.18/0.40    r2_hidden(k1_funct_1(sK2,sK0),sK1) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.18/0.40    inference(cnf_transformation,[],[f6])).
% 0.18/0.40  % SZS output end Proof for theBenchmark
% 0.18/0.40  % (24201)------------------------------
% 0.18/0.40  % (24201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.40  % (24201)Termination reason: Refutation
% 0.18/0.40  
% 0.18/0.40  % (24201)Memory used [KB]: 10618
% 0.18/0.40  % (24201)Time elapsed: 0.006 s
% 0.18/0.40  % (24201)------------------------------
% 0.18/0.40  % (24201)------------------------------
% 0.18/0.41  % (24197)Success in time 0.079 s
%------------------------------------------------------------------------------
