%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 123 expanded)
%              Number of leaves         :   10 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 472 expanded)
%              Number of equality atoms :   47 ( 190 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f50,f55,f60,f65,f68])).

fof(f68,plain,
    ( ~ spl2_5
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_5
    | spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f66,f64])).

fof(f64,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f66,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f54,f59,f25])).

fof(f25,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f59,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_6
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f54,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_5
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f65,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f44,f37,f32,f27,f62])).

fof(f27,plain,
    ( spl2_1
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f37,plain,
    ( spl2_3
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(backward_demodulation,[],[f34,f41])).

fof(f41,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f29,f39,f34,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,
    ( sK0 != k1_relset_1(sK0,sK0,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f29,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f60,plain,
    ( ~ spl2_6
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f43,f37,f32,f27,f57])).

fof(f43,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(backward_demodulation,[],[f39,f41])).

fof(f55,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f45,f37,f32,f27,f52])).

fof(f45,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(backward_demodulation,[],[f29,f41])).

fof(f50,plain,
    ( spl2_4
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f41,f37,f32,f27,f47])).

fof(f47,plain,
    ( spl2_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f40,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f14,f37])).

fof(f14,plain,(
    sK0 != k1_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != k1_relset_1(sK0,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k1_relset_1(X0,X0,X1) != X0
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0) )
   => ( sK0 != k1_relset_1(sK0,sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_relset_1(X0,X0,X1) != X0
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_relset_1(X0,X0,X1) != X0
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
       => k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f12,f27])).

fof(f12,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:19:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (18477)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (18476)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (18484)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (18477)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f30,f35,f40,f50,f55,f60,f65,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~spl2_5 | spl2_6 | ~spl2_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    $false | (~spl2_5 | spl2_6 | ~spl2_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl2_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl2_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_5 | spl2_6)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f54,f59,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.49    inference(equality_resolution,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | spl2_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl2_6 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl2_5 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl2_7 | ~spl2_1 | ~spl2_2 | spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f37,f32,f27,f62])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    spl2_1 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    spl2_3 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 0.22/0.49    inference(backward_demodulation,[],[f34,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | (~spl2_1 | ~spl2_2 | spl2_3)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f29,f39,f34,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK0,sK1) | spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f37])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_funct_2(sK1,sK0,sK0) | ~spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f27])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f32])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ~spl2_6 | ~spl2_1 | ~spl2_2 | spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f37,f32,f27,f57])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 0.22/0.49    inference(backward_demodulation,[],[f39,f41])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl2_5 | ~spl2_1 | ~spl2_2 | spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f37,f32,f27,f52])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 0.22/0.49    inference(backward_demodulation,[],[f29,f41])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl2_4 | ~spl2_1 | ~spl2_2 | spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f37,f32,f27,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    spl2_4 <=> k1_xboole_0 = sK0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ~spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f14,f37])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1] : (k1_relset_1(X0,X0,X1) != X0 & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0)) => (sK0 != k1_relset_1(sK0,sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0,X1] : (k1_relset_1(X0,X0,X1) != X0 & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0))),
% 0.22/0.49    inference(flattening,[],[f5])).
% 0.22/0.49  fof(f5,plain,(
% 0.22/0.49    ? [X0,X1] : (k1_relset_1(X0,X0,X1) != X0 & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,plain,(
% 0.22/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.49    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.49  fof(f3,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.49    inference(negated_conjecture,[],[f2])).
% 0.22/0.49  fof(f2,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f13,f32])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f12,f27])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (18477)------------------------------
% 0.22/0.49  % (18477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18477)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (18477)Memory used [KB]: 1663
% 0.22/0.49  % (18477)Time elapsed: 0.066 s
% 0.22/0.49  % (18477)------------------------------
% 0.22/0.49  % (18477)------------------------------
% 0.22/0.50  % (18469)Success in time 0.13 s
%------------------------------------------------------------------------------
