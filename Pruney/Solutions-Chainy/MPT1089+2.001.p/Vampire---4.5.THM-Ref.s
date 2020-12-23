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
% DateTime   : Thu Dec  3 13:08:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  53 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 173 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f24,f29,f34,f36])).

fof(f36,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f35,f31,f26,f21,f16])).

fof(f16,plain,
    ( spl2_1
  <=> v1_finset_1(k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f21,plain,
    ( spl2_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f26,plain,
    ( spl2_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f31,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f35,plain,
    ( v1_finset_1(k9_relat_1(sK1,sK0))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f23,f28,f33,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f28,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f23,plain,
    ( v1_finset_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f34,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f10,f31])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ v1_finset_1(k9_relat_1(sK1,sK0))
    & v1_finset_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k9_relat_1(X1,X0))
        & v1_finset_1(X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(k9_relat_1(sK1,sK0))
      & v1_finset_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k9_relat_1(X1,X0))
      & v1_finset_1(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k9_relat_1(X1,X0))
      & v1_finset_1(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v1_finset_1(X0)
         => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_finset_1(X0)
       => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_finset_1)).

fof(f29,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f21])).

fof(f12,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f13,f16])).

fof(f13,plain,(
    ~ v1_finset_1(k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (19000)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (19000)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f19,f24,f29,f34,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f35,f31,f26,f21,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    spl2_1 <=> v1_finset_1(k9_relat_1(sK1,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    spl2_2 <=> v1_finset_1(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    spl2_3 <=> v1_funct_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    spl2_4 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    v1_finset_1(k9_relat_1(sK1,sK0)) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f23,f28,f33,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | (~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_finset_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => v1_finset_1(k9_relat_1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    v1_relat_1(sK1) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f31])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    v1_funct_1(sK1) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f26])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    v1_finset_1(sK0) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f21])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f10,f31])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ~v1_finset_1(k9_relat_1(sK1,sK0)) & v1_finset_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1] : (~v1_finset_1(k9_relat_1(X1,X0)) & v1_finset_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v1_finset_1(k9_relat_1(sK1,sK0)) & v1_finset_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ? [X0,X1] : (~v1_finset_1(k9_relat_1(X1,X0)) & v1_finset_1(X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f4])).
% 0.20/0.46  fof(f4,plain,(
% 0.20/0.46    ? [X0,X1] : ((~v1_finset_1(k9_relat_1(X1,X0)) & v1_finset_1(X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_finset_1(X0) => v1_finset_1(k9_relat_1(X1,X0))))),
% 0.20/0.46    inference(negated_conjecture,[],[f2])).
% 0.20/0.46  fof(f2,conjecture,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_finset_1(X0) => v1_finset_1(k9_relat_1(X1,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_finset_1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f11,f26])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    v1_funct_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f12,f21])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    v1_finset_1(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ~spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f13,f16])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ~v1_finset_1(k9_relat_1(sK1,sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (19000)------------------------------
% 0.20/0.46  % (19000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (19000)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (19000)Memory used [KB]: 5245
% 0.20/0.46  % (19000)Time elapsed: 0.057 s
% 0.20/0.46  % (19000)------------------------------
% 0.20/0.46  % (19000)------------------------------
% 0.20/0.46  % (19001)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.46  % (18986)Success in time 0.109 s
%------------------------------------------------------------------------------
