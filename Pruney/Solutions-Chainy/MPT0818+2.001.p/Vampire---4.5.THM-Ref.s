%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  84 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :  124 ( 212 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f48,f53,f58,f64,f66])).

fof(f66,plain,
    ( spl4_7
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f65,f55,f45,f61])).

fof(f61,plain,
    ( spl4_7
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f45,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f55,plain,
    ( spl4_6
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f65,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f47,f57,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f57,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f47,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f64,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f59,f45,f32,f27,f61])).

fof(f27,plain,
    ( spl4_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f32,plain,
    ( spl4_2
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f34,f29,f47,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f29,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f34,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f58,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f41,f37,f55])).

fof(f37,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f41,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f53,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f42,f37,f50])).

fof(f50,plain,
    ( spl4_5
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f42,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f39,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f43,f37,f45])).

fof(f43,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f39,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f40,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & r1_tarski(k2_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & r1_tarski(k2_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & r1_tarski(k2_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_tarski(k2_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f35,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f27])).

fof(f19,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:20:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (8167)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.46  % (8167)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f30,f35,f40,f48,f53,f58,f64,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl4_7 | ~spl4_4 | ~spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f65,f55,f45,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl4_7 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl4_6 <=> v4_relat_1(sK3,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    r1_tarski(k1_relat_1(sK3),sK2) | (~spl4_4 | ~spl4_6)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f47,f57,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    v4_relat_1(sK3,sK2) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f45])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ~spl4_7 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f59,f45,f32,f27,f61])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    spl4_1 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl4_2 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ~r1_tarski(k1_relat_1(sK3),sK2) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f34,f29,f47,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f27])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK3),sK1) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f32])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl4_6 | ~spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f37,f55])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    v4_relat_1(sK3,sK2) | ~spl4_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f39,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f37])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl4_5 | ~spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f42,f37,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl4_5 <=> v5_relat_1(sK3,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    v5_relat_1(sK3,sK0) | ~spl4_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f39,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl4_4 | ~spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f43,f37,f45])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    v1_relat_1(sK3) | ~spl4_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f39,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & r1_tarski(k2_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & r1_tarski(k2_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f32])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f27])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (8167)------------------------------
% 0.21/0.46  % (8167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8167)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (8167)Memory used [KB]: 5373
% 0.21/0.46  % (8167)Time elapsed: 0.058 s
% 0.21/0.46  % (8167)------------------------------
% 0.21/0.46  % (8167)------------------------------
% 0.21/0.46  % (8153)Success in time 0.111 s
%------------------------------------------------------------------------------
