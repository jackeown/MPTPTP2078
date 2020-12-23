%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 116 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  115 ( 282 expanded)
%              Number of equality atoms :   39 ( 132 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f80,f85])).

fof(f85,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f42,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f39,f21])).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f19,f30])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f83,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_2 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2)
    | spl3_2 ),
    inference(superposition,[],[f67,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f67,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_2
  <=> v1_xboole_0(k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f80,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f78,f42])).

fof(f78,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2)
    | spl3_1 ),
    inference(superposition,[],[f74,f33])).

fof(f74,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f71,f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f31,f23])).

fof(f71,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k9_relat_1(sK2,sK1)))
    | ~ v1_xboole_0(k9_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(superposition,[],[f64,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f30,f23])).

fof(f64,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f60,f66,f63])).

fof(f60,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0))) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,sK1) != X0
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(superposition,[],[f34,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f34,plain,(
    ! [X0] :
      ( k7_relset_1(X0,sK0,sK2,sK1) != X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f20,f23])).

fof(f20,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (23824)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (23825)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (23832)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (23817)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (23817)Refutation not found, incomplete strategy% (23817)------------------------------
% 0.20/0.48  % (23817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23831)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (23819)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (23822)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (23821)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (23819)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f68,f80,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    $false | spl3_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f83,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    v1_xboole_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f39,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(resolution,[],[f24,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    inference(backward_demodulation,[],[f19,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ~v1_xboole_0(sK2) | spl3_2),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~v1_xboole_0(sK2) | ~v1_xboole_0(sK2) | spl3_2),
% 0.20/0.49    inference(superposition,[],[f67,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k9_relat_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(superposition,[],[f22,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ~v1_xboole_0(k9_relat_1(sK2,sK1)) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl3_2 <=> v1_xboole_0(k9_relat_1(sK2,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    $false | spl3_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f78,f42])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ~v1_xboole_0(sK2) | spl3_1),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ~v1_xboole_0(sK2) | ~v1_xboole_0(sK2) | spl3_1),
% 0.20/0.49    inference(superposition,[],[f74,f33])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~v1_xboole_0(k9_relat_1(sK2,sK1)) | spl3_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f71,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(superposition,[],[f31,f23])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k9_relat_1(sK2,sK1))) | ~v1_xboole_0(k9_relat_1(sK2,sK1)) | spl3_1),
% 0.20/0.49    inference(superposition,[],[f64,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(superposition,[],[f30,f23])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0))) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f60,f66,f63])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ~v1_xboole_0(k9_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0)))),
% 0.20/0.49    inference(equality_resolution,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (k9_relat_1(sK2,sK1) != X0 | ~v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 0.20/0.49    inference(superposition,[],[f34,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0] : (k7_relset_1(X0,sK0,sK2,sK1) != X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(superposition,[],[f20,f23])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (23819)------------------------------
% 0.20/0.49  % (23819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23819)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (23819)Memory used [KB]: 10618
% 0.20/0.49  % (23819)Time elapsed: 0.081 s
% 0.20/0.49  % (23819)------------------------------
% 0.20/0.49  % (23819)------------------------------
% 0.20/0.49  % (23816)Success in time 0.139 s
%------------------------------------------------------------------------------
