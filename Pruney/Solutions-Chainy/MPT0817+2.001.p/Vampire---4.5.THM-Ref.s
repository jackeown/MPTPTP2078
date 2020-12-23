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
% DateTime   : Thu Dec  3 12:56:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  81 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 222 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f45,f51,f55,f57])).

fof(f57,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | ~ spl4_1 ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(k1_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(k1_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(k1_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( r1_tarski(k1_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f30,plain,
    ( ! [X2,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_1
  <=> ! [X1,X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f55,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f47,f18])).

fof(f47,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | spl4_4 ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f44,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_4
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f46,f18])).

fof(f46,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_3 ),
    inference(resolution,[],[f40,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f40,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f45,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f32,f42,f38])).

fof(f32,plain,
    ( spl4_2
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f36,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f35,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f33,f20])).

fof(f20,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f34,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f27,f32,f29])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f26,f19])).

fof(f19,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X2)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f23,f24])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:56:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (19907)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.19/0.45  % (19920)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.19/0.46  % (19912)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.19/0.46  % (19909)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.19/0.46  % (19915)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (19907)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f34,f45,f51,f55,f57])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    ~spl4_1),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f56])).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    $false | ~spl4_1),
% 0.19/0.46    inference(resolution,[],[f30,f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.19/0.46    inference(cnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.46    inference(flattening,[],[f8])).
% 0.19/0.46  fof(f8,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.19/0.46    inference(negated_conjecture,[],[f5])).
% 0.19/0.46  fof(f5,conjecture,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    spl4_1 <=> ! [X1,X2] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.46  fof(f55,plain,(
% 0.19/0.46    spl4_4),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f53])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    $false | spl4_4),
% 0.19/0.46    inference(resolution,[],[f47,f18])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | spl4_4),
% 0.19/0.46    inference(resolution,[],[f44,f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.46    inference(pure_predicate_removal,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ~v5_relat_1(sK3,sK2) | spl4_4),
% 0.19/0.46    inference(avatar_component_clause,[],[f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    spl4_4 <=> v5_relat_1(sK3,sK2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    spl4_3),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    $false | spl4_3),
% 0.19/0.46    inference(resolution,[],[f46,f18])).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_3),
% 0.19/0.46    inference(resolution,[],[f40,f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ~v1_relat_1(sK3) | spl4_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f38])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    spl4_3 <=> v1_relat_1(sK3)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ~spl4_3 | ~spl4_4 | ~spl4_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f36,f32,f42,f38])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    spl4_2 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ~v5_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | ~spl4_2),
% 0.19/0.46    inference(resolution,[],[f35,f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(nnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ~r1_tarski(k2_relat_1(sK3),sK2) | ~spl4_2),
% 0.19/0.46    inference(resolution,[],[f33,f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.46    inference(cnf_transformation,[],[f16])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k2_relat_1(sK3),X0)) ) | ~spl4_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f32])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    spl4_1 | spl4_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f27,f32,f29])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.19/0.46    inference(resolution,[],[f26,f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    r1_tarski(k1_relat_1(sK3),sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f16])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X0),X2) | ~r1_tarski(k2_relat_1(X0),X1) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.19/0.46    inference(resolution,[],[f23,f24])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (19907)------------------------------
% 0.19/0.46  % (19907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (19907)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (19907)Memory used [KB]: 5373
% 0.19/0.46  % (19907)Time elapsed: 0.063 s
% 0.19/0.46  % (19907)------------------------------
% 0.19/0.46  % (19907)------------------------------
% 0.19/0.47  % (19906)Success in time 0.121 s
%------------------------------------------------------------------------------
