%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:08 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 827 expanded)
%              Number of leaves         :   33 ( 225 expanded)
%              Depth                    :   21
%              Number of atoms          :  719 (4057 expanded)
%              Number of equality atoms :  133 ( 710 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f154,f209,f218,f752,f806,f984,f995,f1079,f1116,f1214,f1221])).

fof(f1221,plain,
    ( spl9_2
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f1220])).

fof(f1220,plain,
    ( $false
    | spl9_2
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1219,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1219,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | spl9_2
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f1218,f872])).

fof(f872,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f871,f181])).

fof(f181,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f74,f175])).

fof(f175,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f165,f72])).

fof(f165,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f91,f143])).

fof(f143,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f92,f136])).

fof(f136,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f75,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

% (29983)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f57,plain,(
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

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

% (29978)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f74,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f871,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f870,f72])).

fof(f870,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f869,f208])).

fof(f208,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl9_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f869,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f860,f121])).

fof(f121,plain,(
    ! [X1] : ~ sP2(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f860,plain,(
    ! [X6] :
      ( sP2(k1_xboole_0,X6)
      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[],[f737,f587])).

fof(f587,plain,(
    ! [X2,X3] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(X3,k1_xboole_0)
      | ~ v1_partfun1(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f437,f117])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f437,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ v1_funct_1(X3)
      | v1_funct_2(X3,X4,X5)
      | ~ v1_partfun1(X3,X4) ) ),
    inference(resolution,[],[f109,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f737,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(k1_xboole_0,X6,X7)
      | sP2(X6,X7)
      | k1_relat_1(k1_xboole_0) = X6 ) ),
    inference(resolution,[],[f513,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f513,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP2(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f511,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X2,X1,X0)
        & sP3(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f48,f47,f46])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f511,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP2(X3,X4)
      | ~ sP3(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f102,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

% (29997)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f1218,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK5)
    | spl9_2
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f646,f488])).

fof(f488,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl9_21
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f646,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK5)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f645,f150])).

fof(f150,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f97,f68])).

fof(f68,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
      | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
      | ~ v1_funct_1(k2_funct_1(sK7)) )
    & sK6 = k2_relset_1(sK5,sK6,sK7)
    & v2_funct_1(sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f50])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
        | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
        | ~ v1_funct_1(k2_funct_1(sK7)) )
      & sK6 = k2_relset_1(sK5,sK6,sK7)
      & v2_funct_1(sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f645,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK5)
    | ~ v1_relat_1(sK7)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f644,f66])).

fof(f66,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f644,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK5)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f642,f69])).

fof(f69,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f642,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK5)
    | ~ v2_funct_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl9_2 ),
    inference(resolution,[],[f625,f316])).

fof(f316,plain,(
    ! [X2,X3] :
      ( sP1(X3,k2_funct_1(X2))
      | ~ r1_tarski(k1_relat_1(X2),X3)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f315,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f315,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),X3)
      | sP1(X3,k2_funct_1(X2))
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f310,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f310,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),X3)
      | sP1(X3,k2_funct_1(X2))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f88,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f625,plain,
    ( ~ sP1(sK5,k2_funct_1(sK7))
    | spl9_2 ),
    inference(resolution,[],[f624,f129])).

fof(f129,plain,
    ( ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl9_2
  <=> v1_funct_2(k2_funct_1(sK7),sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f624,plain,(
    ! [X2] :
      ( v1_funct_2(k2_funct_1(sK7),sK6,X2)
      | ~ sP1(X2,k2_funct_1(sK7)) ) ),
    inference(subsumption_resolution,[],[f623,f150])).

fof(f623,plain,(
    ! [X2] :
      ( v1_funct_2(k2_funct_1(sK7),sK6,X2)
      | ~ sP1(X2,k2_funct_1(sK7))
      | ~ v1_relat_1(sK7) ) ),
    inference(subsumption_resolution,[],[f622,f66])).

fof(f622,plain,(
    ! [X2] :
      ( v1_funct_2(k2_funct_1(sK7),sK6,X2)
      | ~ sP1(X2,k2_funct_1(sK7))
      | ~ v1_funct_1(sK7)
      | ~ v1_relat_1(sK7) ) ),
    inference(subsumption_resolution,[],[f617,f69])).

fof(f617,plain,(
    ! [X2] :
      ( v1_funct_2(k2_funct_1(sK7),sK6,X2)
      | ~ sP1(X2,k2_funct_1(sK7))
      | ~ v2_funct_1(sK7)
      | ~ v1_funct_1(sK7)
      | ~ v1_relat_1(sK7) ) ),
    inference(superposition,[],[f300,f333])).

fof(f333,plain,(
    sK6 = k2_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f331,f68])).

fof(f331,plain,
    ( sK6 = k2_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(superposition,[],[f98,f70])).

fof(f70,plain,(
    sK6 = k2_relset_1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f300,plain,(
    ! [X2,X3] :
      ( v1_funct_2(k2_funct_1(X2),k2_relat_1(X2),X3)
      | ~ sP1(X3,k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f86,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f1214,plain,
    ( ~ spl9_37
    | spl9_3
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f1213,f486,f206,f131,f906])).

fof(f906,plain,
    ( spl9_37
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f131,plain,
    ( spl9_3
  <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1213,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl9_3
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1212,f72])).

fof(f1212,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | ~ v2_funct_1(k1_xboole_0)
    | spl9_3
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f1211,f872])).

fof(f1211,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK5)
    | ~ v2_funct_1(k1_xboole_0)
    | spl9_3
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1210,f148])).

fof(f148,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f97,f73])).

fof(f1210,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK5)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl9_3
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1208,f208])).

fof(f1208,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK5)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl9_3
    | ~ spl9_21 ),
    inference(resolution,[],[f1137,f316])).

fof(f1137,plain,
    ( ~ sP1(sK5,k2_funct_1(k1_xboole_0))
    | spl9_3
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f971,f488])).

fof(f971,plain,
    ( ~ sP1(sK5,k2_funct_1(sK7))
    | spl9_3 ),
    inference(resolution,[],[f970,f133])).

fof(f133,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f970,plain,(
    ! [X2] :
      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
      | ~ sP1(X2,k2_funct_1(sK7)) ) ),
    inference(subsumption_resolution,[],[f969,f150])).

fof(f969,plain,(
    ! [X2] :
      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
      | ~ sP1(X2,k2_funct_1(sK7))
      | ~ v1_relat_1(sK7) ) ),
    inference(subsumption_resolution,[],[f968,f66])).

fof(f968,plain,(
    ! [X2] :
      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
      | ~ sP1(X2,k2_funct_1(sK7))
      | ~ v1_funct_1(sK7)
      | ~ v1_relat_1(sK7) ) ),
    inference(subsumption_resolution,[],[f963,f69])).

fof(f963,plain,(
    ! [X2] :
      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
      | ~ sP1(X2,k2_funct_1(sK7))
      | ~ v2_funct_1(sK7)
      | ~ v1_funct_1(sK7)
      | ~ v1_relat_1(sK7) ) ),
    inference(superposition,[],[f301,f333])).

fof(f301,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k2_funct_1(X4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X4),X5)))
      | ~ sP1(X5,k2_funct_1(X4))
      | ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f87,f82])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1116,plain,
    ( spl9_37
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f1102,f486,f906])).

fof(f1102,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl9_21 ),
    inference(backward_demodulation,[],[f69,f488])).

fof(f1079,plain,
    ( spl9_21
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f1073,f634,f486])).

fof(f634,plain,
    ( spl9_28
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f1073,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_28 ),
    inference(resolution,[],[f1026,f662])).

fof(f662,plain,(
    ! [X0] :
      ( ~ sP1(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f661])).

fof(f661,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | ~ sP1(X3,X2)
      | ~ sP1(k1_xboole_0,X2) ) ),
    inference(duplicate_literal_removal,[],[f660])).

fof(f660,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | ~ sP1(X3,X2)
      | k1_xboole_0 = X2
      | ~ sP1(k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f659,f117])).

fof(f659,plain,(
    ! [X2,X3] :
      ( k2_zfmisc_1(k1_xboole_0,X3) = X2
      | ~ sP1(X3,X2)
      | k1_xboole_0 = X2
      | ~ sP1(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f658,f72])).

fof(f658,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | k2_zfmisc_1(k1_xboole_0,X3) = X2
      | ~ sP1(X3,X2)
      | k1_xboole_0 = X2
      | ~ sP1(k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f656,f117])).

fof(f656,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,X3),X2)
      | k2_zfmisc_1(k1_xboole_0,X3) = X2
      | ~ sP1(X3,X2)
      | k1_xboole_0 = X2
      | ~ sP1(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f239,f413])).

fof(f413,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ sP1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f405,f86])).

fof(f405,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,k1_relat_1(X0),k1_xboole_0)
      | k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ sP1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f120,f250])).

fof(f250,plain,(
    ! [X2,X1] :
      ( sP4(X1,X2,k1_relat_1(X1))
      | ~ sP1(X2,X1) ) ),
    inference(resolution,[],[f107,f87])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f120,plain,(
    ! [X2,X0] :
      ( ~ sP4(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f239,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X5),X4),X5)
      | k2_zfmisc_1(k1_relat_1(X5),X4) = X5
      | ~ sP1(X4,X5) ) ),
    inference(resolution,[],[f227,f91])).

fof(f227,plain,(
    ! [X4,X5] :
      ( r1_tarski(X5,k2_zfmisc_1(k1_relat_1(X5),X4))
      | ~ sP1(X4,X5) ) ),
    inference(resolution,[],[f87,f92])).

fof(f1026,plain,
    ( ! [X0] : sP1(X0,sK7)
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f1007,f72])).

fof(f1007,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | sP1(X0,sK7) )
    | ~ spl9_28 ),
    inference(backward_demodulation,[],[f358,f636])).

fof(f636,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f634])).

fof(f358,plain,(
    ! [X0] :
      ( sP1(X0,sK7)
      | ~ r1_tarski(sK6,X0) ) ),
    inference(subsumption_resolution,[],[f357,f150])).

fof(f357,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6,X0)
      | sP1(X0,sK7)
      | ~ v1_relat_1(sK7) ) ),
    inference(subsumption_resolution,[],[f337,f66])).

fof(f337,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6,X0)
      | sP1(X0,sK7)
      | ~ v1_funct_1(sK7)
      | ~ v1_relat_1(sK7) ) ),
    inference(superposition,[],[f88,f333])).

fof(f995,plain,
    ( spl9_28
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f994,f749,f634])).

fof(f749,plain,
    ( spl9_33
  <=> sP2(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f994,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_33 ),
    inference(resolution,[],[f751,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f751,plain,
    ( sP2(sK5,sK6)
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f749])).

fof(f984,plain,
    ( spl9_3
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f983])).

fof(f983,plain,
    ( $false
    | spl9_3
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f971,f817])).

fof(f817,plain,
    ( sP1(sK5,k2_funct_1(sK7))
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f816,f150])).

fof(f816,plain,
    ( sP1(sK5,k2_funct_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f815,f66])).

fof(f815,plain,
    ( sP1(sK5,k2_funct_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f779,f69])).

fof(f779,plain,
    ( sP1(sK5,k2_funct_1(sK7))
    | ~ v2_funct_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl9_32 ),
    inference(superposition,[],[f318,f747])).

fof(f747,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f745])).

fof(f745,plain,
    ( spl9_32
  <=> sK5 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f318,plain,(
    ! [X7] :
      ( sP1(k1_relat_1(X7),k2_funct_1(X7))
      | ~ v2_funct_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f317,f80])).

fof(f317,plain,(
    ! [X7] :
      ( sP1(k1_relat_1(X7),k2_funct_1(X7))
      | ~ v1_relat_1(k2_funct_1(X7))
      | ~ v2_funct_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f314,f81])).

fof(f314,plain,(
    ! [X7] :
      ( sP1(k1_relat_1(X7),k2_funct_1(X7))
      | ~ v1_funct_1(k2_funct_1(X7))
      | ~ v1_relat_1(k2_funct_1(X7))
      | ~ v2_funct_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f266,f83])).

fof(f266,plain,(
    ! [X0] :
      ( sP1(k2_relat_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f88,f114])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f806,plain,
    ( spl9_2
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f805])).

fof(f805,plain,
    ( $false
    | spl9_2
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f804,f150])).

fof(f804,plain,
    ( ~ v1_relat_1(sK7)
    | spl9_2
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f803,f66])).

fof(f803,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl9_2
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f802,f69])).

fof(f802,plain,
    ( ~ v2_funct_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl9_2
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f779,f625])).

fof(f752,plain,
    ( spl9_32
    | spl9_33 ),
    inference(avatar_split_clause,[],[f743,f749,f745])).

fof(f743,plain,
    ( sP2(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f739,f67])).

fof(f67,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f739,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP2(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(resolution,[],[f513,f68])).

fof(f218,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f212,f111])).

fof(f111,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( v2_funct_1(sK8)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f9,f64])).

fof(f64,plain,
    ( ? [X0] :
        ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v2_funct_1(sK8)
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_1)).

fof(f212,plain,
    ( ~ v1_relat_1(sK8)
    | ~ spl9_6 ),
    inference(resolution,[],[f204,f112])).

fof(f112,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f204,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl9_6
  <=> ! [X3] :
        ( ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f209,plain,
    ( spl9_6
    | spl9_7 ),
    inference(avatar_split_clause,[],[f199,f206,f203])).

fof(f199,plain,(
    ! [X3] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f84,f73])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f154,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f150,f139])).

fof(f139,plain,
    ( ~ v1_relat_1(sK7)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f138,f66])).

fof(f138,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl9_1 ),
    inference(resolution,[],[f81,f125])).

fof(f125,plain,
    ( ~ v1_funct_1(k2_funct_1(sK7))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl9_1
  <=> v1_funct_1(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f134,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f71,f131,f127,f123])).

fof(f71,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | ~ v1_funct_1(k2_funct_1(sK7)) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (29982)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.29/0.54  % (29980)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.29/0.54  % (29981)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.29/0.55  % (29998)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.50/0.56  % (29989)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.50/0.56  % (29988)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.50/0.57  % (29982)Refutation found. Thanks to Tanya!
% 1.50/0.57  % SZS status Theorem for theBenchmark
% 1.50/0.57  % (30003)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f1225,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(avatar_sat_refutation,[],[f134,f154,f209,f218,f752,f806,f984,f995,f1079,f1116,f1214,f1221])).
% 1.50/0.57  fof(f1221,plain,(
% 1.50/0.57    spl9_2 | ~spl9_7 | ~spl9_21),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f1220])).
% 1.50/0.57  fof(f1220,plain,(
% 1.50/0.57    $false | (spl9_2 | ~spl9_7 | ~spl9_21)),
% 1.50/0.57    inference(subsumption_resolution,[],[f1219,f72])).
% 1.50/0.57  fof(f72,plain,(
% 1.50/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.50/0.57  fof(f1219,plain,(
% 1.50/0.57    ~r1_tarski(k1_xboole_0,sK5) | (spl9_2 | ~spl9_7 | ~spl9_21)),
% 1.50/0.57    inference(forward_demodulation,[],[f1218,f872])).
% 1.50/0.57  fof(f872,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl9_7),
% 1.50/0.57    inference(subsumption_resolution,[],[f871,f181])).
% 1.50/0.57  fof(f181,plain,(
% 1.50/0.57    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(superposition,[],[f74,f175])).
% 1.50/0.57  fof(f175,plain,(
% 1.50/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f165,f72])).
% 1.50/0.57  fof(f165,plain,(
% 1.50/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))),
% 1.50/0.57    inference(resolution,[],[f91,f143])).
% 1.50/0.57  fof(f143,plain,(
% 1.50/0.57    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)),
% 1.50/0.57    inference(resolution,[],[f92,f136])).
% 1.50/0.57  fof(f136,plain,(
% 1.50/0.57    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.50/0.57    inference(superposition,[],[f75,f116])).
% 1.50/0.57  fof(f116,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.50/0.57    inference(equality_resolution,[],[f96])).
% 1.50/0.57  fof(f96,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f58])).
% 1.50/0.57  fof(f58,plain,(
% 1.50/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.50/0.57    inference(flattening,[],[f57])).
% 1.50/0.57  % (29983)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.50/0.57  fof(f57,plain,(
% 1.50/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.50/0.57    inference(nnf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.57  fof(f75,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f16])).
% 1.50/0.57  fof(f16,axiom,(
% 1.50/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.50/0.57  fof(f92,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f56])).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.50/0.57    inference(nnf_transformation,[],[f5])).
% 1.50/0.57  fof(f5,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.50/0.57  fof(f91,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f55])).
% 1.50/0.57  fof(f55,plain,(
% 1.50/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.57    inference(flattening,[],[f54])).
% 1.50/0.57  % (29978)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.50/0.57  fof(f54,plain,(
% 1.50/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.57    inference(nnf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.57  fof(f74,plain,(
% 1.50/0.57    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f16])).
% 1.50/0.57  fof(f871,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl9_7),
% 1.50/0.57    inference(subsumption_resolution,[],[f870,f72])).
% 1.50/0.57  fof(f870,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl9_7),
% 1.50/0.57    inference(subsumption_resolution,[],[f869,f208])).
% 1.50/0.57  fof(f208,plain,(
% 1.50/0.57    v1_funct_1(k1_xboole_0) | ~spl9_7),
% 1.50/0.57    inference(avatar_component_clause,[],[f206])).
% 1.50/0.57  fof(f206,plain,(
% 1.50/0.57    spl9_7 <=> v1_funct_1(k1_xboole_0)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.50/0.57  fof(f869,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f860,f121])).
% 1.50/0.57  fof(f121,plain,(
% 1.50/0.57    ( ! [X1] : (~sP2(k1_xboole_0,X1)) )),
% 1.50/0.57    inference(equality_resolution,[],[f105])).
% 1.50/0.57  fof(f105,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP2(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f63])).
% 1.50/0.57  fof(f63,plain,(
% 1.50/0.57    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 1.50/0.57    inference(nnf_transformation,[],[f46])).
% 1.50/0.57  fof(f46,plain,(
% 1.50/0.57    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 1.50/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.50/0.57  fof(f860,plain,(
% 1.50/0.57    ( ! [X6] : (sP2(k1_xboole_0,X6) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0)) )),
% 1.50/0.57    inference(resolution,[],[f737,f587])).
% 1.50/0.57  fof(f587,plain,(
% 1.50/0.57    ( ! [X2,X3] : (v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_1(X3) | ~r1_tarski(X3,k1_xboole_0) | ~v1_partfun1(X3,k1_xboole_0)) )),
% 1.50/0.57    inference(superposition,[],[f437,f117])).
% 1.50/0.57  fof(f117,plain,(
% 1.50/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.50/0.57    inference(equality_resolution,[],[f95])).
% 1.50/0.57  fof(f95,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f58])).
% 1.50/0.57  fof(f437,plain,(
% 1.50/0.57    ( ! [X4,X5,X3] : (~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~v1_funct_1(X3) | v1_funct_2(X3,X4,X5) | ~v1_partfun1(X3,X4)) )),
% 1.50/0.57    inference(resolution,[],[f109,f93])).
% 1.50/0.57  fof(f93,plain,(
% 1.50/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f56])).
% 1.50/0.57  fof(f109,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f39])).
% 1.50/0.57  fof(f39,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(flattening,[],[f38])).
% 1.50/0.57  fof(f38,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f14])).
% 1.50/0.57  fof(f14,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 1.50/0.57  fof(f737,plain,(
% 1.50/0.57    ( ! [X6,X7] : (~v1_funct_2(k1_xboole_0,X6,X7) | sP2(X6,X7) | k1_relat_1(k1_xboole_0) = X6) )),
% 1.50/0.57    inference(resolution,[],[f513,f73])).
% 1.50/0.57  fof(f73,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f4])).
% 1.50/0.57  fof(f4,axiom,(
% 1.50/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.50/0.57  fof(f513,plain,(
% 1.50/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP2(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f511,f106])).
% 1.50/0.57  fof(f106,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X2,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f49])).
% 1.50/0.57  fof(f49,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(definition_folding,[],[f37,f48,f47,f46])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 1.50/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.50/0.57  fof(f48,plain,(
% 1.50/0.57    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 1.50/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.50/0.57  fof(f37,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(flattening,[],[f36])).
% 1.50/0.57  fof(f36,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f15])).
% 1.50/0.57  fof(f15,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.50/0.57  fof(f511,plain,(
% 1.50/0.57    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP2(X3,X4) | ~sP3(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.50/0.57    inference(superposition,[],[f102,f99])).
% 1.50/0.57  fof(f99,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f35])).
% 1.50/0.57  % (29997)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f12])).
% 1.50/0.57  fof(f12,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.50/0.57  fof(f102,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP2(X0,X2) | ~sP3(X0,X1,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f62])).
% 1.50/0.57  fof(f62,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP2(X0,X2) | ~sP3(X0,X1,X2))),
% 1.50/0.57    inference(rectify,[],[f61])).
% 1.50/0.57  fof(f61,plain,(
% 1.50/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 1.50/0.57    inference(nnf_transformation,[],[f47])).
% 1.50/0.57  fof(f1218,plain,(
% 1.50/0.57    ~r1_tarski(k1_relat_1(k1_xboole_0),sK5) | (spl9_2 | ~spl9_21)),
% 1.50/0.57    inference(forward_demodulation,[],[f646,f488])).
% 1.50/0.57  fof(f488,plain,(
% 1.50/0.57    k1_xboole_0 = sK7 | ~spl9_21),
% 1.50/0.57    inference(avatar_component_clause,[],[f486])).
% 1.50/0.57  fof(f486,plain,(
% 1.50/0.57    spl9_21 <=> k1_xboole_0 = sK7),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.50/0.57  fof(f646,plain,(
% 1.50/0.57    ~r1_tarski(k1_relat_1(sK7),sK5) | spl9_2),
% 1.50/0.57    inference(subsumption_resolution,[],[f645,f150])).
% 1.50/0.57  fof(f150,plain,(
% 1.50/0.57    v1_relat_1(sK7)),
% 1.50/0.57    inference(resolution,[],[f97,f68])).
% 1.50/0.57  fof(f68,plain,(
% 1.50/0.57    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.50/0.57    inference(cnf_transformation,[],[f51])).
% 1.50/0.57  fof(f51,plain,(
% 1.50/0.57    (~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))) & sK6 = k2_relset_1(sK5,sK6,sK7) & v2_funct_1(sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f50])).
% 1.50/0.57  fof(f50,plain,(
% 1.50/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))) & sK6 = k2_relset_1(sK5,sK6,sK7) & v2_funct_1(sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.50/0.57    inference(flattening,[],[f21])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.50/0.57    inference(ennf_transformation,[],[f20])).
% 1.50/0.57  fof(f20,negated_conjecture,(
% 1.50/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.50/0.57    inference(negated_conjecture,[],[f19])).
% 1.50/0.57  fof(f19,conjecture,(
% 1.50/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.50/0.57  fof(f97,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f33])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.50/0.57  fof(f645,plain,(
% 1.50/0.57    ~r1_tarski(k1_relat_1(sK7),sK5) | ~v1_relat_1(sK7) | spl9_2),
% 1.50/0.57    inference(subsumption_resolution,[],[f644,f66])).
% 1.50/0.57  fof(f66,plain,(
% 1.50/0.57    v1_funct_1(sK7)),
% 1.50/0.57    inference(cnf_transformation,[],[f51])).
% 1.50/0.57  fof(f644,plain,(
% 1.50/0.57    ~r1_tarski(k1_relat_1(sK7),sK5) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl9_2),
% 1.50/0.57    inference(subsumption_resolution,[],[f642,f69])).
% 1.50/0.57  fof(f69,plain,(
% 1.50/0.57    v2_funct_1(sK7)),
% 1.50/0.57    inference(cnf_transformation,[],[f51])).
% 1.50/0.57  fof(f642,plain,(
% 1.50/0.57    ~r1_tarski(k1_relat_1(sK7),sK5) | ~v2_funct_1(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl9_2),
% 1.50/0.57    inference(resolution,[],[f625,f316])).
% 1.50/0.57  fof(f316,plain,(
% 1.50/0.57    ( ! [X2,X3] : (sP1(X3,k2_funct_1(X2)) | ~r1_tarski(k1_relat_1(X2),X3) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f315,f80])).
% 1.50/0.57  fof(f80,plain,(
% 1.50/0.57    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f26])).
% 1.50/0.57  fof(f26,plain,(
% 1.50/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.57    inference(flattening,[],[f25])).
% 1.50/0.57  fof(f25,plain,(
% 1.50/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.50/0.57  fof(f315,plain,(
% 1.50/0.57    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),X3) | sP1(X3,k2_funct_1(X2)) | ~v1_relat_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f310,f81])).
% 1.50/0.57  fof(f81,plain,(
% 1.50/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f26])).
% 1.50/0.57  fof(f310,plain,(
% 1.50/0.57    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),X3) | sP1(X3,k2_funct_1(X2)) | ~v1_funct_1(k2_funct_1(X2)) | ~v1_relat_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.57    inference(superposition,[],[f88,f83])).
% 1.50/0.57  fof(f83,plain,(
% 1.50/0.57    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f28])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.57    inference(flattening,[],[f27])).
% 1.50/0.57  fof(f27,plain,(
% 1.50/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,axiom,(
% 1.50/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.50/0.57  fof(f88,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f45])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    ! [X0,X1] : (sP1(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.57    inference(definition_folding,[],[f32,f44])).
% 1.50/0.57  fof(f44,plain,(
% 1.50/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 1.50/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.57    inference(flattening,[],[f31])).
% 1.50/0.58  fof(f31,plain,(
% 1.50/0.58    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.58    inference(ennf_transformation,[],[f18])).
% 1.50/0.58  fof(f18,axiom,(
% 1.50/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.50/0.58  fof(f625,plain,(
% 1.50/0.58    ~sP1(sK5,k2_funct_1(sK7)) | spl9_2),
% 1.50/0.58    inference(resolution,[],[f624,f129])).
% 1.50/0.58  fof(f129,plain,(
% 1.50/0.58    ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | spl9_2),
% 1.50/0.58    inference(avatar_component_clause,[],[f127])).
% 1.50/0.58  fof(f127,plain,(
% 1.50/0.58    spl9_2 <=> v1_funct_2(k2_funct_1(sK7),sK6,sK5)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.50/0.58  fof(f624,plain,(
% 1.50/0.58    ( ! [X2] : (v1_funct_2(k2_funct_1(sK7),sK6,X2) | ~sP1(X2,k2_funct_1(sK7))) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f623,f150])).
% 1.50/0.58  fof(f623,plain,(
% 1.50/0.58    ( ! [X2] : (v1_funct_2(k2_funct_1(sK7),sK6,X2) | ~sP1(X2,k2_funct_1(sK7)) | ~v1_relat_1(sK7)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f622,f66])).
% 1.50/0.58  fof(f622,plain,(
% 1.50/0.58    ( ! [X2] : (v1_funct_2(k2_funct_1(sK7),sK6,X2) | ~sP1(X2,k2_funct_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f617,f69])).
% 1.50/0.58  fof(f617,plain,(
% 1.50/0.58    ( ! [X2] : (v1_funct_2(k2_funct_1(sK7),sK6,X2) | ~sP1(X2,k2_funct_1(sK7)) | ~v2_funct_1(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) )),
% 1.50/0.58    inference(superposition,[],[f300,f333])).
% 1.50/0.58  fof(f333,plain,(
% 1.50/0.58    sK6 = k2_relat_1(sK7)),
% 1.50/0.58    inference(subsumption_resolution,[],[f331,f68])).
% 1.50/0.58  fof(f331,plain,(
% 1.50/0.58    sK6 = k2_relat_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.50/0.58    inference(superposition,[],[f98,f70])).
% 1.50/0.58  fof(f70,plain,(
% 1.50/0.58    sK6 = k2_relset_1(sK5,sK6,sK7)),
% 1.50/0.58    inference(cnf_transformation,[],[f51])).
% 1.50/0.58  fof(f98,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f34])).
% 1.50/0.58  fof(f34,plain,(
% 1.50/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.58    inference(ennf_transformation,[],[f13])).
% 1.50/0.58  fof(f13,axiom,(
% 1.50/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.50/0.58  fof(f300,plain,(
% 1.50/0.58    ( ! [X2,X3] : (v1_funct_2(k2_funct_1(X2),k2_relat_1(X2),X3) | ~sP1(X3,k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.58    inference(superposition,[],[f86,f82])).
% 1.50/0.58  fof(f82,plain,(
% 1.50/0.58    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f28])).
% 1.50/0.58  fof(f86,plain,(
% 1.50/0.58    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP1(X0,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f53])).
% 1.50/0.58  fof(f53,plain,(
% 1.50/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 1.50/0.58    inference(nnf_transformation,[],[f44])).
% 1.50/0.58  fof(f1214,plain,(
% 1.50/0.58    ~spl9_37 | spl9_3 | ~spl9_7 | ~spl9_21),
% 1.50/0.58    inference(avatar_split_clause,[],[f1213,f486,f206,f131,f906])).
% 1.50/0.58  fof(f906,plain,(
% 1.50/0.58    spl9_37 <=> v2_funct_1(k1_xboole_0)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 1.50/0.58  fof(f131,plain,(
% 1.50/0.58    spl9_3 <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.50/0.58  fof(f1213,plain,(
% 1.50/0.58    ~v2_funct_1(k1_xboole_0) | (spl9_3 | ~spl9_7 | ~spl9_21)),
% 1.50/0.58    inference(subsumption_resolution,[],[f1212,f72])).
% 1.50/0.58  fof(f1212,plain,(
% 1.50/0.58    ~r1_tarski(k1_xboole_0,sK5) | ~v2_funct_1(k1_xboole_0) | (spl9_3 | ~spl9_7 | ~spl9_21)),
% 1.50/0.58    inference(forward_demodulation,[],[f1211,f872])).
% 1.50/0.58  fof(f1211,plain,(
% 1.50/0.58    ~r1_tarski(k1_relat_1(k1_xboole_0),sK5) | ~v2_funct_1(k1_xboole_0) | (spl9_3 | ~spl9_7 | ~spl9_21)),
% 1.50/0.58    inference(subsumption_resolution,[],[f1210,f148])).
% 1.50/0.58  fof(f148,plain,(
% 1.50/0.58    v1_relat_1(k1_xboole_0)),
% 1.50/0.58    inference(resolution,[],[f97,f73])).
% 1.50/0.58  fof(f1210,plain,(
% 1.50/0.58    ~r1_tarski(k1_relat_1(k1_xboole_0),sK5) | ~v2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (spl9_3 | ~spl9_7 | ~spl9_21)),
% 1.50/0.58    inference(subsumption_resolution,[],[f1208,f208])).
% 1.50/0.58  fof(f1208,plain,(
% 1.50/0.58    ~r1_tarski(k1_relat_1(k1_xboole_0),sK5) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (spl9_3 | ~spl9_21)),
% 1.50/0.58    inference(resolution,[],[f1137,f316])).
% 1.50/0.58  fof(f1137,plain,(
% 1.50/0.58    ~sP1(sK5,k2_funct_1(k1_xboole_0)) | (spl9_3 | ~spl9_21)),
% 1.50/0.58    inference(forward_demodulation,[],[f971,f488])).
% 1.50/0.58  fof(f971,plain,(
% 1.50/0.58    ~sP1(sK5,k2_funct_1(sK7)) | spl9_3),
% 1.50/0.58    inference(resolution,[],[f970,f133])).
% 1.50/0.58  fof(f133,plain,(
% 1.50/0.58    ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | spl9_3),
% 1.50/0.58    inference(avatar_component_clause,[],[f131])).
% 1.50/0.58  fof(f970,plain,(
% 1.50/0.58    ( ! [X2] : (m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X2))) | ~sP1(X2,k2_funct_1(sK7))) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f969,f150])).
% 1.50/0.58  fof(f969,plain,(
% 1.50/0.58    ( ! [X2] : (m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X2))) | ~sP1(X2,k2_funct_1(sK7)) | ~v1_relat_1(sK7)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f968,f66])).
% 1.50/0.58  fof(f968,plain,(
% 1.50/0.58    ( ! [X2] : (m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X2))) | ~sP1(X2,k2_funct_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f963,f69])).
% 1.50/0.58  fof(f963,plain,(
% 1.50/0.58    ( ! [X2] : (m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X2))) | ~sP1(X2,k2_funct_1(sK7)) | ~v2_funct_1(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) )),
% 1.50/0.58    inference(superposition,[],[f301,f333])).
% 1.50/0.58  fof(f301,plain,(
% 1.50/0.58    ( ! [X4,X5] : (m1_subset_1(k2_funct_1(X4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X4),X5))) | ~sP1(X5,k2_funct_1(X4)) | ~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 1.50/0.58    inference(superposition,[],[f87,f82])).
% 1.50/0.58  fof(f87,plain,(
% 1.50/0.58    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP1(X0,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f53])).
% 1.50/0.58  fof(f1116,plain,(
% 1.50/0.58    spl9_37 | ~spl9_21),
% 1.50/0.58    inference(avatar_split_clause,[],[f1102,f486,f906])).
% 1.50/0.58  fof(f1102,plain,(
% 1.50/0.58    v2_funct_1(k1_xboole_0) | ~spl9_21),
% 1.50/0.58    inference(backward_demodulation,[],[f69,f488])).
% 1.50/0.58  fof(f1079,plain,(
% 1.50/0.58    spl9_21 | ~spl9_28),
% 1.50/0.58    inference(avatar_split_clause,[],[f1073,f634,f486])).
% 1.50/0.58  fof(f634,plain,(
% 1.50/0.58    spl9_28 <=> k1_xboole_0 = sK6),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 1.50/0.58  fof(f1073,plain,(
% 1.50/0.58    k1_xboole_0 = sK7 | ~spl9_28),
% 1.50/0.58    inference(resolution,[],[f1026,f662])).
% 1.50/0.58  fof(f662,plain,(
% 1.50/0.58    ( ! [X0] : (~sP1(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.50/0.58    inference(condensation,[],[f661])).
% 1.50/0.58  fof(f661,plain,(
% 1.50/0.58    ( ! [X2,X3] : (k1_xboole_0 = X2 | ~sP1(X3,X2) | ~sP1(k1_xboole_0,X2)) )),
% 1.50/0.58    inference(duplicate_literal_removal,[],[f660])).
% 1.50/0.58  fof(f660,plain,(
% 1.50/0.58    ( ! [X2,X3] : (k1_xboole_0 = X2 | ~sP1(X3,X2) | k1_xboole_0 = X2 | ~sP1(k1_xboole_0,X2)) )),
% 1.50/0.58    inference(forward_demodulation,[],[f659,f117])).
% 1.50/0.58  fof(f659,plain,(
% 1.50/0.58    ( ! [X2,X3] : (k2_zfmisc_1(k1_xboole_0,X3) = X2 | ~sP1(X3,X2) | k1_xboole_0 = X2 | ~sP1(k1_xboole_0,X2)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f658,f72])).
% 1.50/0.58  fof(f658,plain,(
% 1.50/0.58    ( ! [X2,X3] : (~r1_tarski(k1_xboole_0,X2) | k2_zfmisc_1(k1_xboole_0,X3) = X2 | ~sP1(X3,X2) | k1_xboole_0 = X2 | ~sP1(k1_xboole_0,X2)) )),
% 1.50/0.58    inference(forward_demodulation,[],[f656,f117])).
% 1.50/0.58  fof(f656,plain,(
% 1.50/0.58    ( ! [X2,X3] : (~r1_tarski(k2_zfmisc_1(k1_xboole_0,X3),X2) | k2_zfmisc_1(k1_xboole_0,X3) = X2 | ~sP1(X3,X2) | k1_xboole_0 = X2 | ~sP1(k1_xboole_0,X2)) )),
% 1.50/0.58    inference(superposition,[],[f239,f413])).
% 1.50/0.58  fof(f413,plain,(
% 1.50/0.58    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 = X0 | ~sP1(k1_xboole_0,X0)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f405,f86])).
% 1.50/0.58  fof(f405,plain,(
% 1.50/0.58    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(X0),k1_xboole_0) | k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 = X0 | ~sP1(k1_xboole_0,X0)) )),
% 1.50/0.58    inference(resolution,[],[f120,f250])).
% 1.50/0.58  fof(f250,plain,(
% 1.50/0.58    ( ! [X2,X1] : (sP4(X1,X2,k1_relat_1(X1)) | ~sP1(X2,X1)) )),
% 1.50/0.58    inference(resolution,[],[f107,f87])).
% 1.50/0.58  fof(f107,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X2,X1,X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f49])).
% 1.50/0.58  fof(f120,plain,(
% 1.50/0.58    ( ! [X2,X0] : (~sP4(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 1.50/0.58    inference(equality_resolution,[],[f100])).
% 1.50/0.58  fof(f100,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP4(X0,X1,X2)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f60])).
% 1.50/0.58  fof(f60,plain,(
% 1.50/0.58    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP4(X0,X1,X2))),
% 1.50/0.58    inference(rectify,[],[f59])).
% 1.50/0.58  fof(f59,plain,(
% 1.50/0.58    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 1.50/0.58    inference(nnf_transformation,[],[f48])).
% 1.50/0.58  fof(f239,plain,(
% 1.50/0.58    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(X5),X4),X5) | k2_zfmisc_1(k1_relat_1(X5),X4) = X5 | ~sP1(X4,X5)) )),
% 1.50/0.58    inference(resolution,[],[f227,f91])).
% 1.50/0.58  fof(f227,plain,(
% 1.50/0.58    ( ! [X4,X5] : (r1_tarski(X5,k2_zfmisc_1(k1_relat_1(X5),X4)) | ~sP1(X4,X5)) )),
% 1.50/0.58    inference(resolution,[],[f87,f92])).
% 1.50/0.58  fof(f1026,plain,(
% 1.50/0.58    ( ! [X0] : (sP1(X0,sK7)) ) | ~spl9_28),
% 1.50/0.58    inference(subsumption_resolution,[],[f1007,f72])).
% 1.50/0.58  fof(f1007,plain,(
% 1.50/0.58    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | sP1(X0,sK7)) ) | ~spl9_28),
% 1.50/0.58    inference(backward_demodulation,[],[f358,f636])).
% 1.50/0.58  fof(f636,plain,(
% 1.50/0.58    k1_xboole_0 = sK6 | ~spl9_28),
% 1.50/0.58    inference(avatar_component_clause,[],[f634])).
% 1.50/0.58  fof(f358,plain,(
% 1.50/0.58    ( ! [X0] : (sP1(X0,sK7) | ~r1_tarski(sK6,X0)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f357,f150])).
% 1.50/0.58  fof(f357,plain,(
% 1.50/0.58    ( ! [X0] : (~r1_tarski(sK6,X0) | sP1(X0,sK7) | ~v1_relat_1(sK7)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f337,f66])).
% 1.50/0.58  fof(f337,plain,(
% 1.50/0.58    ( ! [X0] : (~r1_tarski(sK6,X0) | sP1(X0,sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) )),
% 1.50/0.58    inference(superposition,[],[f88,f333])).
% 1.50/0.58  fof(f995,plain,(
% 1.50/0.58    spl9_28 | ~spl9_33),
% 1.50/0.58    inference(avatar_split_clause,[],[f994,f749,f634])).
% 1.50/0.58  fof(f749,plain,(
% 1.50/0.58    spl9_33 <=> sP2(sK5,sK6)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 1.50/0.58  fof(f994,plain,(
% 1.50/0.58    k1_xboole_0 = sK6 | ~spl9_33),
% 1.50/0.58    inference(resolution,[],[f751,f104])).
% 1.50/0.58  fof(f104,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~sP2(X0,X1) | k1_xboole_0 = X1) )),
% 1.50/0.58    inference(cnf_transformation,[],[f63])).
% 1.50/0.58  fof(f751,plain,(
% 1.50/0.58    sP2(sK5,sK6) | ~spl9_33),
% 1.50/0.58    inference(avatar_component_clause,[],[f749])).
% 1.50/0.58  fof(f984,plain,(
% 1.50/0.58    spl9_3 | ~spl9_32),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f983])).
% 1.50/0.58  fof(f983,plain,(
% 1.50/0.58    $false | (spl9_3 | ~spl9_32)),
% 1.50/0.58    inference(subsumption_resolution,[],[f971,f817])).
% 1.50/0.58  fof(f817,plain,(
% 1.50/0.58    sP1(sK5,k2_funct_1(sK7)) | ~spl9_32),
% 1.50/0.58    inference(subsumption_resolution,[],[f816,f150])).
% 1.50/0.58  fof(f816,plain,(
% 1.50/0.58    sP1(sK5,k2_funct_1(sK7)) | ~v1_relat_1(sK7) | ~spl9_32),
% 1.50/0.58    inference(subsumption_resolution,[],[f815,f66])).
% 1.50/0.58  fof(f815,plain,(
% 1.50/0.58    sP1(sK5,k2_funct_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl9_32),
% 1.50/0.58    inference(subsumption_resolution,[],[f779,f69])).
% 1.50/0.58  fof(f779,plain,(
% 1.50/0.58    sP1(sK5,k2_funct_1(sK7)) | ~v2_funct_1(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl9_32),
% 1.50/0.58    inference(superposition,[],[f318,f747])).
% 1.50/0.58  fof(f747,plain,(
% 1.50/0.58    sK5 = k1_relat_1(sK7) | ~spl9_32),
% 1.50/0.58    inference(avatar_component_clause,[],[f745])).
% 1.50/0.58  fof(f745,plain,(
% 1.50/0.58    spl9_32 <=> sK5 = k1_relat_1(sK7)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 1.50/0.58  fof(f318,plain,(
% 1.50/0.58    ( ! [X7] : (sP1(k1_relat_1(X7),k2_funct_1(X7)) | ~v2_funct_1(X7) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f317,f80])).
% 1.50/0.58  fof(f317,plain,(
% 1.50/0.58    ( ! [X7] : (sP1(k1_relat_1(X7),k2_funct_1(X7)) | ~v1_relat_1(k2_funct_1(X7)) | ~v2_funct_1(X7) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f314,f81])).
% 1.50/0.58  fof(f314,plain,(
% 1.50/0.58    ( ! [X7] : (sP1(k1_relat_1(X7),k2_funct_1(X7)) | ~v1_funct_1(k2_funct_1(X7)) | ~v1_relat_1(k2_funct_1(X7)) | ~v2_funct_1(X7) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 1.50/0.58    inference(superposition,[],[f266,f83])).
% 1.50/0.58  fof(f266,plain,(
% 1.50/0.58    ( ! [X0] : (sP1(k2_relat_1(X0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(resolution,[],[f88,f114])).
% 1.50/0.58  fof(f114,plain,(
% 1.50/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.58    inference(equality_resolution,[],[f90])).
% 1.50/0.58  fof(f90,plain,(
% 1.50/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.58    inference(cnf_transformation,[],[f55])).
% 1.50/0.58  fof(f806,plain,(
% 1.50/0.58    spl9_2 | ~spl9_32),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f805])).
% 1.50/0.58  fof(f805,plain,(
% 1.50/0.58    $false | (spl9_2 | ~spl9_32)),
% 1.50/0.58    inference(subsumption_resolution,[],[f804,f150])).
% 1.50/0.58  fof(f804,plain,(
% 1.50/0.58    ~v1_relat_1(sK7) | (spl9_2 | ~spl9_32)),
% 1.50/0.58    inference(subsumption_resolution,[],[f803,f66])).
% 1.50/0.58  fof(f803,plain,(
% 1.50/0.58    ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | (spl9_2 | ~spl9_32)),
% 1.50/0.58    inference(subsumption_resolution,[],[f802,f69])).
% 1.50/0.58  fof(f802,plain,(
% 1.50/0.58    ~v2_funct_1(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | (spl9_2 | ~spl9_32)),
% 1.50/0.58    inference(subsumption_resolution,[],[f779,f625])).
% 1.50/0.58  fof(f752,plain,(
% 1.50/0.58    spl9_32 | spl9_33),
% 1.50/0.58    inference(avatar_split_clause,[],[f743,f749,f745])).
% 1.50/0.58  fof(f743,plain,(
% 1.50/0.58    sP2(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 1.50/0.58    inference(subsumption_resolution,[],[f739,f67])).
% 1.50/0.58  fof(f67,plain,(
% 1.50/0.58    v1_funct_2(sK7,sK5,sK6)),
% 1.50/0.58    inference(cnf_transformation,[],[f51])).
% 1.50/0.58  fof(f739,plain,(
% 1.50/0.58    ~v1_funct_2(sK7,sK5,sK6) | sP2(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 1.50/0.58    inference(resolution,[],[f513,f68])).
% 1.50/0.58  fof(f218,plain,(
% 1.50/0.58    ~spl9_6),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f217])).
% 1.50/0.58  fof(f217,plain,(
% 1.50/0.58    $false | ~spl9_6),
% 1.50/0.58    inference(subsumption_resolution,[],[f212,f111])).
% 1.50/0.58  fof(f111,plain,(
% 1.50/0.58    v1_relat_1(sK8)),
% 1.50/0.58    inference(cnf_transformation,[],[f65])).
% 1.50/0.58  fof(f65,plain,(
% 1.50/0.58    v2_funct_1(sK8) & v1_funct_1(sK8) & v1_relat_1(sK8)),
% 1.50/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f9,f64])).
% 1.50/0.58  fof(f64,plain,(
% 1.50/0.58    ? [X0] : (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(sK8) & v1_funct_1(sK8) & v1_relat_1(sK8))),
% 1.50/0.58    introduced(choice_axiom,[])).
% 1.50/0.58  fof(f9,axiom,(
% 1.50/0.58    ? [X0] : (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_1)).
% 1.50/0.58  fof(f212,plain,(
% 1.50/0.58    ~v1_relat_1(sK8) | ~spl9_6),
% 1.50/0.58    inference(resolution,[],[f204,f112])).
% 1.50/0.58  fof(f112,plain,(
% 1.50/0.58    v1_funct_1(sK8)),
% 1.50/0.58    inference(cnf_transformation,[],[f65])).
% 1.50/0.58  fof(f204,plain,(
% 1.50/0.58    ( ! [X3] : (~v1_funct_1(X3) | ~v1_relat_1(X3)) ) | ~spl9_6),
% 1.50/0.58    inference(avatar_component_clause,[],[f203])).
% 1.50/0.58  fof(f203,plain,(
% 1.50/0.58    spl9_6 <=> ! [X3] : (~v1_funct_1(X3) | ~v1_relat_1(X3))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.50/0.58  fof(f209,plain,(
% 1.50/0.58    spl9_6 | spl9_7),
% 1.50/0.58    inference(avatar_split_clause,[],[f199,f206,f203])).
% 1.50/0.58  fof(f199,plain,(
% 1.50/0.58    ( ! [X3] : (v1_funct_1(k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.50/0.58    inference(resolution,[],[f84,f73])).
% 1.50/0.58  fof(f84,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f30])).
% 1.50/0.58  fof(f30,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(flattening,[],[f29])).
% 1.50/0.58  fof(f29,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.58    inference(ennf_transformation,[],[f7])).
% 1.50/0.58  fof(f7,axiom,(
% 1.50/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).
% 1.50/0.58  fof(f154,plain,(
% 1.50/0.58    spl9_1),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f153])).
% 1.50/0.58  fof(f153,plain,(
% 1.50/0.58    $false | spl9_1),
% 1.50/0.58    inference(subsumption_resolution,[],[f150,f139])).
% 1.50/0.58  fof(f139,plain,(
% 1.50/0.58    ~v1_relat_1(sK7) | spl9_1),
% 1.50/0.58    inference(subsumption_resolution,[],[f138,f66])).
% 1.50/0.58  fof(f138,plain,(
% 1.50/0.58    ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl9_1),
% 1.50/0.58    inference(resolution,[],[f81,f125])).
% 1.50/0.58  fof(f125,plain,(
% 1.50/0.58    ~v1_funct_1(k2_funct_1(sK7)) | spl9_1),
% 1.50/0.58    inference(avatar_component_clause,[],[f123])).
% 1.50/0.58  fof(f123,plain,(
% 1.50/0.58    spl9_1 <=> v1_funct_1(k2_funct_1(sK7))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.50/0.58  fof(f134,plain,(
% 1.50/0.58    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 1.50/0.58    inference(avatar_split_clause,[],[f71,f131,f127,f123])).
% 1.50/0.58  fof(f71,plain,(
% 1.50/0.58    ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))),
% 1.50/0.58    inference(cnf_transformation,[],[f51])).
% 1.50/0.58  % SZS output end Proof for theBenchmark
% 1.50/0.58  % (29982)------------------------------
% 1.50/0.58  % (29982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (29982)Termination reason: Refutation
% 1.50/0.58  
% 1.50/0.58  % (29982)Memory used [KB]: 6652
% 1.50/0.58  % (29982)Time elapsed: 0.143 s
% 1.50/0.58  % (29982)------------------------------
% 1.50/0.58  % (29982)------------------------------
% 1.50/0.58  % (29995)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.50/0.58  % (29996)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.50/0.58  % (29977)Success in time 0.215 s
%------------------------------------------------------------------------------
