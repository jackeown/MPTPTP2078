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
% DateTime   : Thu Dec  3 13:03:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 141 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  146 ( 356 expanded)
%              Number of equality atoms :   42 ( 171 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f66,f96,f104,f115])).

fof(f115,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f113,f21])).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f113,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f44,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X1,X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_1
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(k2_zfmisc_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f104,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f56,f99])).

fof(f99,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_4 ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2)
    | spl3_4 ),
    inference(superposition,[],[f65,f33])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f65,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_4
  <=> v1_xboole_0(k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f49,f31])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

fof(f49,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f40,f21])).

fof(f40,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[],[f24,f29])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f96,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f94,f47])).

fof(f47,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_3 ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2)
    | spl3_3 ),
    inference(superposition,[],[f90,f33])).

fof(f90,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,sK1))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f87,f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f31,f23])).

fof(f87,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k9_relat_1(sK2,sK1)))
    | ~ v1_xboole_0(k9_relat_1(sK2,sK1))
    | spl3_3 ),
    inference(superposition,[],[f62,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f30,f23])).

fof(f62,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f59,f64,f61])).

fof(f59,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0))) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,sK1) != X0
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(superposition,[],[f34,f28])).

% (16156)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f34,plain,(
    ! [X0] :
      ( k7_relset_1(X0,sK0,sK2,sK1) != X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f20,f23])).

fof(f20,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f39,f46,f43])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK2)
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X0)) ) ),
    inference(resolution,[],[f24,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (16172)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (16166)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.46  % (16155)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.47  % (16172)Refutation not found, incomplete strategy% (16172)------------------------------
% 0.19/0.47  % (16172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (16172)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (16172)Memory used [KB]: 10490
% 0.19/0.47  % (16172)Time elapsed: 0.065 s
% 0.19/0.47  % (16172)------------------------------
% 0.19/0.47  % (16172)------------------------------
% 0.19/0.48  % (16164)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (16151)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.50  % (16151)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f117,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f48,f66,f96,f104,f115])).
% 0.19/0.50  fof(f115,plain,(
% 0.19/0.50    ~spl3_1),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f114])).
% 0.19/0.50  fof(f114,plain,(
% 0.19/0.50    $false | ~spl3_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f113,f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    v1_xboole_0(k1_xboole_0)),
% 0.19/0.50    inference(cnf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    v1_xboole_0(k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.50  fof(f113,plain,(
% 0.19/0.50    ~v1_xboole_0(k1_xboole_0) | ~spl3_1),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f107])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | ~spl3_1),
% 0.19/0.50    inference(superposition,[],[f44,f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(equality_resolution,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.50    inference(flattening,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.50    inference(nnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X1,X0)) | ~v1_xboole_0(X0)) ) | ~spl3_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    spl3_1 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~v1_xboole_0(k2_zfmisc_1(X1,X0)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    spl3_4),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f103])).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    $false | spl3_4),
% 0.19/0.50    inference(subsumption_resolution,[],[f56,f99])).
% 0.19/0.50  fof(f99,plain,(
% 0.19/0.50    ~v1_xboole_0(sK2) | spl3_4),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f98])).
% 0.19/0.50  fof(f98,plain,(
% 0.19/0.50    ~v1_xboole_0(sK2) | ~v1_xboole_0(sK2) | spl3_4),
% 0.19/0.50    inference(superposition,[],[f65,f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k9_relat_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.50    inference(superposition,[],[f22,f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ~v1_xboole_0(k9_relat_1(sK2,sK1)) | spl3_4),
% 0.19/0.50    inference(avatar_component_clause,[],[f64])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    spl3_4 <=> v1_xboole_0(k9_relat_1(sK2,sK1))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    v1_xboole_0(sK2)),
% 0.19/0.50    inference(resolution,[],[f49,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.50    inference(backward_demodulation,[],[f19,f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.50    inference(equality_resolution,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.19/0.50  fof(f9,plain,(
% 0.19/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.50  fof(f8,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.50    inference(negated_conjecture,[],[f7])).
% 0.19/0.50  fof(f7,conjecture,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f40,f21])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X1) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.19/0.50    inference(superposition,[],[f24,f29])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.19/0.50  fof(f96,plain,(
% 0.19/0.50    ~spl3_2 | spl3_3),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f95])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    $false | (~spl3_2 | spl3_3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f94,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    v1_xboole_0(sK2) | ~spl3_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    spl3_2 <=> v1_xboole_0(sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    ~v1_xboole_0(sK2) | spl3_3),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f93])).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    ~v1_xboole_0(sK2) | ~v1_xboole_0(sK2) | spl3_3),
% 0.19/0.50    inference(superposition,[],[f90,f33])).
% 0.19/0.50  fof(f90,plain,(
% 0.19/0.50    ~v1_xboole_0(k9_relat_1(sK2,sK1)) | spl3_3),
% 0.19/0.50    inference(subsumption_resolution,[],[f87,f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.19/0.50    inference(superposition,[],[f31,f23])).
% 0.19/0.50  fof(f87,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k9_relat_1(sK2,sK1))) | ~v1_xboole_0(k9_relat_1(sK2,sK1)) | spl3_3),
% 0.19/0.50    inference(superposition,[],[f62,f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.50    inference(superposition,[],[f30,f23])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0))) | spl3_3),
% 0.19/0.50    inference(avatar_component_clause,[],[f61])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    ~spl3_3 | ~spl3_4),
% 0.19/0.50    inference(avatar_split_clause,[],[f59,f64,f61])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ~v1_xboole_0(k9_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(sK2,sK1),sK0)))),
% 0.19/0.50    inference(equality_resolution,[],[f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X0] : (k9_relat_1(sK2,sK1) != X0 | ~v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 0.19/0.50    inference(superposition,[],[f34,f28])).
% 0.19/0.50  % (16156)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ( ! [X0] : (k7_relset_1(X0,sK0,sK2,sK1) != X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.50    inference(superposition,[],[f20,f23])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    spl3_1 | spl3_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f39,f46,f43])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v1_xboole_0(sK2) | ~v1_xboole_0(X0) | ~v1_xboole_0(k2_zfmisc_1(X1,X0))) )),
% 0.19/0.50    inference(resolution,[],[f24,f36])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (16151)------------------------------
% 0.19/0.50  % (16151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (16151)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (16151)Memory used [KB]: 10618
% 0.19/0.50  % (16151)Time elapsed: 0.083 s
% 0.19/0.50  % (16151)------------------------------
% 0.19/0.50  % (16151)------------------------------
% 0.19/0.50  % (16165)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.50  % (16143)Success in time 0.147 s
%------------------------------------------------------------------------------
