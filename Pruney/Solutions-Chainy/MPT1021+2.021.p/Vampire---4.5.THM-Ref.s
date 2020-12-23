%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 418 expanded)
%              Number of leaves         :   41 ( 174 expanded)
%              Depth                    :   11
%              Number of atoms          :  671 (1423 expanded)
%              Number of equality atoms :  123 ( 211 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14261)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f130,f135,f195,f224,f244,f284,f289,f294,f299,f327,f358,f399,f404,f446,f455,f470,f537,f539,f575,f643,f651,f655])).

fof(f655,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f651,plain,
    ( ~ spl2_35
    | spl2_36
    | ~ spl2_42 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | ~ spl2_35
    | spl2_36
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f644,f545])).

fof(f545,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl2_36 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl2_36
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f644,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl2_35
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f536,f642,f115])).

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f109,f104])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f109,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

% (14262)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (14263)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (14257)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (14256)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (14248)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (14249)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f642,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f640])).

fof(f640,plain,
    ( spl2_42
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f536,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl2_35
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f643,plain,
    ( spl2_42
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f613,f476,f355,f132,f640])).

fof(f132,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f355,plain,
    ( spl2_18
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f476,plain,
    ( spl2_33
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f613,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f579,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f579,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(backward_demodulation,[],[f134,f576])).

fof(f576,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(backward_demodulation,[],[f357,f478])).

fof(f478,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f476])).

fof(f357,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f355])).

fof(f134,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f575,plain,
    ( ~ spl2_25
    | spl2_28
    | ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl2_25
    | spl2_28
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f571,f200])).

fof(f200,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) ),
    inference(unit_resulting_resolution,[],[f65,f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f571,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl2_25
    | spl2_28
    | ~ spl2_30 ),
    inference(backward_demodulation,[],[f454,f569])).

fof(f569,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_25
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f398,f465])).

fof(f465,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl2_30
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f398,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl2_25
  <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f454,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | spl2_28 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl2_28
  <=> r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f539,plain,
    ( sK0 != k2_relat_1(sK1)
    | k1_xboole_0 != sK0
    | k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f537,plain,
    ( spl2_35
    | ~ spl2_2
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f483,f467,f122,f534])).

fof(f122,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f467,plain,
    ( spl2_31
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f483,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f124,f469])).

fof(f469,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f467])).

fof(f124,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f470,plain,
    ( spl2_30
    | spl2_31
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f253,f132,f122,f467,f463])).

fof(f253,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f248,f124])).

fof(f248,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f85,f134])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f455,plain,
    ( ~ spl2_28
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | spl2_13
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f442,f401,f324,f286,f221,f192,f132,f117,f452])).

fof(f117,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f192,plain,
    ( spl2_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f221,plain,
    ( spl2_8
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f286,plain,
    ( spl2_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f324,plain,
    ( spl2_16
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f401,plain,
    ( spl2_26
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f442,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | spl2_13
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f288,f441])).

fof(f441,plain,
    ( k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f419,f232])).

fof(f232,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f194,f119,f223,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f62])).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f223,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f119,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f194,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f192])).

fof(f419,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f119,f134,f326,f403,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f403,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f401])).

fof(f326,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f324])).

fof(f288,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f286])).

fof(f446,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | spl2_14
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | spl2_14
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f444,f200])).

fof(f444,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | spl2_14
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f293,f443])).

fof(f443,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f417,f329])).

fof(f329,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f233,f328])).

fof(f328,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f194,f283,f298,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f298,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl2_15
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f283,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl2_12
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f233,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f194,f119,f223,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f62])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f417,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f119,f326,f134,f403,f97])).

fof(f293,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl2_14
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f404,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f319,f132,f127,f122,f117,f401])).

fof(f127,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f319,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f306,f275])).

fof(f275,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f119,f124,f129,f134,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f129,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f306,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f119,f124,f129,f134,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f399,plain,
    ( spl2_25
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f209,f132,f396])).

fof(f209,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f134,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f358,plain,
    ( spl2_18
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f328,f296,f281,f192,f355])).

fof(f327,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f277,f132,f127,f122,f117,f324])).

fof(f277,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f267,f275])).

fof(f267,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f119,f124,f129,f134,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f299,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f230,f132,f127,f117,f296])).

fof(f230,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f119,f129,f134,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f294,plain,
    ( ~ spl2_14
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10 ),
    inference(avatar_split_clause,[],[f279,f241,f132,f127,f122,f117,f291])).

fof(f241,plain,
    ( spl2_10
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f279,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10 ),
    inference(backward_demodulation,[],[f243,f275])).

fof(f243,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f241])).

fof(f289,plain,
    ( ~ spl2_13
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(avatar_split_clause,[],[f278,f237,f132,f127,f122,f117,f286])).

fof(f237,plain,
    ( spl2_9
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f278,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(backward_demodulation,[],[f239,f275])).

fof(f239,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f237])).

fof(f284,plain,
    ( spl2_12
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f178,f132,f281])).

fof(f178,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f134,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f244,plain,
    ( ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f59,f241,f237])).

fof(f59,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f47])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f224,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f218,f132,f127,f117,f221])).

fof(f218,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f119,f129,f134,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f195,plain,
    ( spl2_7
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f160,f132,f192])).

fof(f160,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f134,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f135,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f58,f132])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f130,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f57,f127])).

fof(f57,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f125,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f56,f122])).

fof(f56,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f120,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f55,f117])).

fof(f55,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (14238)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.48  % (14250)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.48  % (14247)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.49  % (14266)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.50  % (14255)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.50  % (14258)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.51  % (14239)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (14245)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (14242)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (14254)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (14246)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (14254)Refutation not found, incomplete strategy% (14254)------------------------------
% 0.20/0.53  % (14254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14240)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (14254)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14254)Memory used [KB]: 10746
% 0.20/0.53  % (14254)Time elapsed: 0.123 s
% 0.20/0.53  % (14254)------------------------------
% 0.20/0.53  % (14254)------------------------------
% 0.20/0.53  % (14241)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (14253)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (14260)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (14252)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (14251)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (14244)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (14264)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (14259)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (14243)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (14267)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (14265)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (14258)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (14261)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  fof(f656,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f120,f125,f130,f135,f195,f224,f244,f284,f289,f294,f299,f327,f358,f399,f404,f446,f455,f470,f537,f539,f575,f643,f651,f655])).
% 0.20/0.54  fof(f655,plain,(
% 0.20/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.54  fof(f651,plain,(
% 0.20/0.54    ~spl2_35 | spl2_36 | ~spl2_42),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f650])).
% 0.20/0.54  fof(f650,plain,(
% 0.20/0.54    $false | (~spl2_35 | spl2_36 | ~spl2_42)),
% 0.20/0.54    inference(subsumption_resolution,[],[f644,f545])).
% 0.20/0.54  fof(f545,plain,(
% 0.20/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | spl2_36),
% 0.20/0.54    inference(avatar_component_clause,[],[f544])).
% 0.20/0.54  fof(f544,plain,(
% 0.20/0.54    spl2_36 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.20/0.54  fof(f644,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (~spl2_35 | ~spl2_42)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f536,f642,f115])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f109,f104])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(flattening,[],[f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.54    inference(equality_resolution,[],[f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  % (14262)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (14263)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (14257)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (14256)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (14248)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (14249)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.56  fof(f642,plain,(
% 0.20/0.56    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl2_42),
% 0.20/0.56    inference(avatar_component_clause,[],[f640])).
% 0.20/0.56  fof(f640,plain,(
% 0.20/0.56    spl2_42 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.20/0.56  fof(f536,plain,(
% 0.20/0.56    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_35),
% 0.20/0.56    inference(avatar_component_clause,[],[f534])).
% 0.20/0.56  fof(f534,plain,(
% 0.20/0.56    spl2_35 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.20/0.56  fof(f643,plain,(
% 0.20/0.56    spl2_42 | ~spl2_4 | ~spl2_18 | ~spl2_33),
% 0.20/0.56    inference(avatar_split_clause,[],[f613,f476,f355,f132,f640])).
% 0.20/0.56  fof(f132,plain,(
% 0.20/0.56    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.56  fof(f355,plain,(
% 0.20/0.56    spl2_18 <=> sK0 = k2_relat_1(sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.56  fof(f476,plain,(
% 0.20/0.56    spl2_33 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.20/0.56  fof(f613,plain,(
% 0.20/0.56    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | (~spl2_4 | ~spl2_18 | ~spl2_33)),
% 0.20/0.56    inference(forward_demodulation,[],[f579,f103])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f80])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f52])).
% 0.20/0.56  fof(f579,plain,(
% 0.20/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_4 | ~spl2_18 | ~spl2_33)),
% 0.20/0.56    inference(backward_demodulation,[],[f134,f576])).
% 0.20/0.56  fof(f576,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | (~spl2_18 | ~spl2_33)),
% 0.20/0.56    inference(backward_demodulation,[],[f357,f478])).
% 0.20/0.56  fof(f478,plain,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(sK1) | ~spl2_33),
% 0.20/0.56    inference(avatar_component_clause,[],[f476])).
% 0.20/0.56  fof(f357,plain,(
% 0.20/0.56    sK0 = k2_relat_1(sK1) | ~spl2_18),
% 0.20/0.56    inference(avatar_component_clause,[],[f355])).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f132])).
% 0.20/0.56  fof(f575,plain,(
% 0.20/0.56    ~spl2_25 | spl2_28 | ~spl2_30),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f574])).
% 0.20/0.56  fof(f574,plain,(
% 0.20/0.56    $false | (~spl2_25 | spl2_28 | ~spl2_30)),
% 0.20/0.56    inference(subsumption_resolution,[],[f571,f200])).
% 0.20/0.56  fof(f200,plain,(
% 0.20/0.56    ( ! [X0] : (r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f65,f111])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f110])).
% 0.20/0.56  fof(f110,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.56    inference(equality_resolution,[],[f96])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(flattening,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.54/0.56  fof(f65,plain,(
% 1.54/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f17])).
% 1.54/0.56  fof(f17,axiom,(
% 1.54/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.54/0.56  fof(f571,plain,(
% 1.54/0.56    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (~spl2_25 | spl2_28 | ~spl2_30)),
% 1.54/0.56    inference(backward_demodulation,[],[f454,f569])).
% 1.54/0.56  fof(f569,plain,(
% 1.54/0.56    sK0 = k1_relat_1(sK1) | (~spl2_25 | ~spl2_30)),
% 1.54/0.56    inference(forward_demodulation,[],[f398,f465])).
% 1.54/0.56  fof(f465,plain,(
% 1.54/0.56    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_30),
% 1.54/0.56    inference(avatar_component_clause,[],[f463])).
% 1.54/0.56  fof(f463,plain,(
% 1.54/0.56    spl2_30 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 1.54/0.56  fof(f398,plain,(
% 1.54/0.56    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) | ~spl2_25),
% 1.54/0.56    inference(avatar_component_clause,[],[f396])).
% 1.54/0.56  fof(f396,plain,(
% 1.54/0.56    spl2_25 <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 1.54/0.56  fof(f454,plain,(
% 1.54/0.56    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | spl2_28),
% 1.54/0.56    inference(avatar_component_clause,[],[f452])).
% 1.54/0.56  fof(f452,plain,(
% 1.54/0.56    spl2_28 <=> r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.54/0.56  fof(f539,plain,(
% 1.54/0.56    sK0 != k2_relat_1(sK1) | k1_xboole_0 != sK0 | k1_xboole_0 = k2_relat_1(sK1)),
% 1.54/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.56  fof(f537,plain,(
% 1.54/0.56    spl2_35 | ~spl2_2 | ~spl2_31),
% 1.54/0.56    inference(avatar_split_clause,[],[f483,f467,f122,f534])).
% 1.54/0.56  fof(f122,plain,(
% 1.54/0.56    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.54/0.56  fof(f467,plain,(
% 1.54/0.56    spl2_31 <=> k1_xboole_0 = sK0),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.54/0.56  fof(f483,plain,(
% 1.54/0.56    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_2 | ~spl2_31)),
% 1.54/0.56    inference(backward_demodulation,[],[f124,f469])).
% 1.54/0.56  fof(f469,plain,(
% 1.54/0.56    k1_xboole_0 = sK0 | ~spl2_31),
% 1.54/0.56    inference(avatar_component_clause,[],[f467])).
% 1.54/0.56  fof(f124,plain,(
% 1.54/0.56    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 1.54/0.56    inference(avatar_component_clause,[],[f122])).
% 1.54/0.56  fof(f470,plain,(
% 1.54/0.56    spl2_30 | spl2_31 | ~spl2_2 | ~spl2_4),
% 1.54/0.56    inference(avatar_split_clause,[],[f253,f132,f122,f467,f463])).
% 1.54/0.56  fof(f253,plain,(
% 1.54/0.56    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl2_2 | ~spl2_4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f248,f124])).
% 1.54/0.56  fof(f248,plain,(
% 1.54/0.56    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_4),
% 1.54/0.56    inference(resolution,[],[f85,f134])).
% 1.54/0.56  fof(f85,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f53])).
% 1.54/0.56  fof(f455,plain,(
% 1.54/0.56    ~spl2_28 | ~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_8 | spl2_13 | ~spl2_16 | ~spl2_26),
% 1.54/0.56    inference(avatar_split_clause,[],[f442,f401,f324,f286,f221,f192,f132,f117,f452])).
% 1.54/0.56  fof(f117,plain,(
% 1.54/0.56    spl2_1 <=> v1_funct_1(sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.54/0.56  fof(f192,plain,(
% 1.54/0.56    spl2_7 <=> v1_relat_1(sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.54/0.56  fof(f221,plain,(
% 1.54/0.56    spl2_8 <=> v2_funct_1(sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.54/0.56  fof(f286,plain,(
% 1.54/0.56    spl2_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.54/0.56  fof(f324,plain,(
% 1.54/0.56    spl2_16 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.54/0.56  fof(f401,plain,(
% 1.54/0.56    spl2_26 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.54/0.56  fof(f442,plain,(
% 1.54/0.56    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_8 | spl2_13 | ~spl2_16 | ~spl2_26)),
% 1.54/0.56    inference(backward_demodulation,[],[f288,f441])).
% 1.54/0.56  fof(f441,plain,(
% 1.54/0.56    k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_16 | ~spl2_26)),
% 1.54/0.56    inference(forward_demodulation,[],[f419,f232])).
% 1.54/0.56  fof(f232,plain,(
% 1.54/0.56    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | (~spl2_1 | ~spl2_7 | ~spl2_8)),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f194,f119,f223,f101])).
% 1.54/0.56  fof(f101,plain,(
% 1.54/0.56    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f67,f62])).
% 1.54/0.56  fof(f62,plain,(
% 1.54/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f20])).
% 1.54/0.56  fof(f20,axiom,(
% 1.54/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.54/0.56  fof(f67,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(flattening,[],[f26])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.56    inference(ennf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.54/0.56  fof(f223,plain,(
% 1.54/0.56    v2_funct_1(sK1) | ~spl2_8),
% 1.54/0.56    inference(avatar_component_clause,[],[f221])).
% 1.54/0.56  fof(f119,plain,(
% 1.54/0.56    v1_funct_1(sK1) | ~spl2_1),
% 1.54/0.56    inference(avatar_component_clause,[],[f117])).
% 1.54/0.56  fof(f194,plain,(
% 1.54/0.56    v1_relat_1(sK1) | ~spl2_7),
% 1.54/0.56    inference(avatar_component_clause,[],[f192])).
% 1.54/0.56  fof(f419,plain,(
% 1.54/0.56    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_16 | ~spl2_26)),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f119,f134,f326,f403,f97])).
% 1.54/0.56  fof(f97,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f46])).
% 1.54/0.56  fof(f46,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.56    inference(flattening,[],[f45])).
% 1.54/0.56  fof(f45,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.56    inference(ennf_transformation,[],[f18])).
% 1.54/0.56  fof(f18,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.54/0.56  fof(f403,plain,(
% 1.54/0.56    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_26),
% 1.54/0.56    inference(avatar_component_clause,[],[f401])).
% 1.54/0.56  fof(f326,plain,(
% 1.54/0.56    v1_funct_1(k2_funct_1(sK1)) | ~spl2_16),
% 1.54/0.56    inference(avatar_component_clause,[],[f324])).
% 1.54/0.56  fof(f288,plain,(
% 1.54/0.56    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl2_13),
% 1.54/0.56    inference(avatar_component_clause,[],[f286])).
% 1.54/0.56  fof(f446,plain,(
% 1.54/0.56    ~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_12 | spl2_14 | ~spl2_15 | ~spl2_16 | ~spl2_26),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f445])).
% 1.54/0.56  fof(f445,plain,(
% 1.54/0.56    $false | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_12 | spl2_14 | ~spl2_15 | ~spl2_16 | ~spl2_26)),
% 1.54/0.56    inference(subsumption_resolution,[],[f444,f200])).
% 1.54/0.56  fof(f444,plain,(
% 1.54/0.56    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_12 | spl2_14 | ~spl2_15 | ~spl2_16 | ~spl2_26)),
% 1.54/0.56    inference(backward_demodulation,[],[f293,f443])).
% 1.54/0.56  fof(f443,plain,(
% 1.54/0.56    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_12 | ~spl2_15 | ~spl2_16 | ~spl2_26)),
% 1.54/0.56    inference(forward_demodulation,[],[f417,f329])).
% 1.54/0.56  fof(f329,plain,(
% 1.54/0.56    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_7 | ~spl2_8 | ~spl2_12 | ~spl2_15)),
% 1.54/0.56    inference(backward_demodulation,[],[f233,f328])).
% 1.54/0.56  fof(f328,plain,(
% 1.54/0.56    sK0 = k2_relat_1(sK1) | (~spl2_7 | ~spl2_12 | ~spl2_15)),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f194,f283,f298,f69])).
% 1.54/0.56  fof(f69,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f49])).
% 1.54/0.56  fof(f49,plain,(
% 1.54/0.56    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(nnf_transformation,[],[f29])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(flattening,[],[f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.54/0.56    inference(ennf_transformation,[],[f15])).
% 1.54/0.56  fof(f15,axiom,(
% 1.54/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.54/0.56  fof(f298,plain,(
% 1.54/0.56    v2_funct_2(sK1,sK0) | ~spl2_15),
% 1.54/0.56    inference(avatar_component_clause,[],[f296])).
% 1.54/0.56  fof(f296,plain,(
% 1.54/0.56    spl2_15 <=> v2_funct_2(sK1,sK0)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.54/0.56  fof(f283,plain,(
% 1.54/0.56    v5_relat_1(sK1,sK0) | ~spl2_12),
% 1.54/0.56    inference(avatar_component_clause,[],[f281])).
% 1.54/0.56  fof(f281,plain,(
% 1.54/0.56    spl2_12 <=> v5_relat_1(sK1,sK0)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.54/0.56  fof(f233,plain,(
% 1.54/0.56    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | (~spl2_1 | ~spl2_7 | ~spl2_8)),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f194,f119,f223,f100])).
% 1.54/0.57  fof(f100,plain,(
% 1.54/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f68,f62])).
% 1.54/0.57  fof(f68,plain,(
% 1.54/0.57    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f27])).
% 1.54/0.57  fof(f417,plain,(
% 1.54/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_16 | ~spl2_26)),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f119,f326,f134,f403,f97])).
% 1.54/0.57  fof(f293,plain,(
% 1.54/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl2_14),
% 1.54/0.57    inference(avatar_component_clause,[],[f291])).
% 1.54/0.57  fof(f291,plain,(
% 1.54/0.57    spl2_14 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.54/0.57  fof(f404,plain,(
% 1.54/0.57    spl2_26 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f319,f132,f127,f122,f117,f401])).
% 1.54/0.57  fof(f127,plain,(
% 1.54/0.57    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.54/0.57  fof(f319,plain,(
% 1.54/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.54/0.57    inference(forward_demodulation,[],[f306,f275])).
% 1.54/0.57  fof(f275,plain,(
% 1.54/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f119,f124,f129,f134,f71])).
% 1.54/0.57  fof(f71,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f31])).
% 1.54/0.57  fof(f31,plain,(
% 1.54/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.54/0.57    inference(flattening,[],[f30])).
% 1.54/0.57  fof(f30,plain,(
% 1.54/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f19])).
% 1.54/0.57  fof(f19,axiom,(
% 1.54/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.54/0.57  fof(f129,plain,(
% 1.54/0.57    v3_funct_2(sK1,sK0,sK0) | ~spl2_3),
% 1.54/0.57    inference(avatar_component_clause,[],[f127])).
% 1.54/0.57  fof(f306,plain,(
% 1.54/0.57    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f119,f124,f129,f134,f75])).
% 1.54/0.57  fof(f75,plain,(
% 1.54/0.57    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.54/0.57    inference(flattening,[],[f32])).
% 1.54/0.57  fof(f32,plain,(
% 1.54/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f16])).
% 1.54/0.57  fof(f16,axiom,(
% 1.54/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.54/0.57  fof(f399,plain,(
% 1.54/0.57    spl2_25 | ~spl2_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f209,f132,f396])).
% 1.54/0.57  fof(f209,plain,(
% 1.54/0.57    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) | ~spl2_4),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f134,f82])).
% 1.54/0.57  fof(f82,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f35])).
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f11])).
% 1.54/0.57  fof(f11,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.54/0.57  fof(f358,plain,(
% 1.54/0.57    spl2_18 | ~spl2_7 | ~spl2_12 | ~spl2_15),
% 1.54/0.57    inference(avatar_split_clause,[],[f328,f296,f281,f192,f355])).
% 1.54/0.57  fof(f327,plain,(
% 1.54/0.57    spl2_16 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f277,f132,f127,f122,f117,f324])).
% 1.54/0.57  fof(f277,plain,(
% 1.54/0.57    v1_funct_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.54/0.57    inference(backward_demodulation,[],[f267,f275])).
% 1.54/0.57  fof(f267,plain,(
% 1.54/0.57    v1_funct_1(k2_funct_2(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f119,f124,f129,f134,f72])).
% 1.54/0.57  fof(f72,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f33])).
% 1.54/0.57  fof(f299,plain,(
% 1.54/0.57    spl2_15 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f230,f132,f127,f117,f296])).
% 1.54/0.57  fof(f230,plain,(
% 1.54/0.57    v2_funct_2(sK1,sK0) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f119,f129,f134,f93])).
% 1.54/0.57  fof(f93,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f40])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(flattening,[],[f39])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f13])).
% 1.54/0.57  fof(f13,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.54/0.57  fof(f294,plain,(
% 1.54/0.57    ~spl2_14 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_10),
% 1.54/0.57    inference(avatar_split_clause,[],[f279,f241,f132,f127,f122,f117,f291])).
% 1.54/0.57  fof(f241,plain,(
% 1.54/0.57    spl2_10 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.54/0.57  fof(f279,plain,(
% 1.54/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_10)),
% 1.54/0.57    inference(backward_demodulation,[],[f243,f275])).
% 1.54/0.57  fof(f243,plain,(
% 1.54/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | spl2_10),
% 1.54/0.57    inference(avatar_component_clause,[],[f241])).
% 1.54/0.57  fof(f289,plain,(
% 1.54/0.57    ~spl2_13 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_9),
% 1.54/0.57    inference(avatar_split_clause,[],[f278,f237,f132,f127,f122,f117,f286])).
% 1.54/0.57  fof(f237,plain,(
% 1.54/0.57    spl2_9 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.54/0.57  fof(f278,plain,(
% 1.54/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_9)),
% 1.54/0.57    inference(backward_demodulation,[],[f239,f275])).
% 1.54/0.57  fof(f239,plain,(
% 1.54/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl2_9),
% 1.54/0.57    inference(avatar_component_clause,[],[f237])).
% 1.54/0.57  fof(f284,plain,(
% 1.54/0.57    spl2_12 | ~spl2_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f178,f132,f281])).
% 1.54/0.57  fof(f178,plain,(
% 1.54/0.57    v5_relat_1(sK1,sK0) | ~spl2_4),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f134,f84])).
% 1.54/0.57  fof(f84,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f36])).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.54/0.57  fof(f244,plain,(
% 1.54/0.57    ~spl2_9 | ~spl2_10),
% 1.54/0.57    inference(avatar_split_clause,[],[f59,f241,f237])).
% 1.54/0.57  fof(f59,plain,(
% 1.54/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.54/0.57    inference(cnf_transformation,[],[f48])).
% 1.54/0.57  fof(f48,plain,(
% 1.54/0.57    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f47])).
% 1.54/0.57  fof(f47,plain,(
% 1.54/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.54/0.57    inference(flattening,[],[f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f22])).
% 1.54/0.57  fof(f22,negated_conjecture,(
% 1.54/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.54/0.57    inference(negated_conjecture,[],[f21])).
% 1.54/0.57  fof(f21,conjecture,(
% 1.54/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 1.54/0.57  fof(f224,plain,(
% 1.54/0.57    spl2_8 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f218,f132,f127,f117,f221])).
% 1.54/0.57  fof(f218,plain,(
% 1.54/0.57    v2_funct_1(sK1) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f119,f129,f134,f92])).
% 1.54/0.57  fof(f92,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f40])).
% 1.54/0.57  fof(f195,plain,(
% 1.54/0.57    spl2_7 | ~spl2_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f160,f132,f192])).
% 1.54/0.57  fof(f160,plain,(
% 1.54/0.57    v1_relat_1(sK1) | ~spl2_4),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f134,f81])).
% 1.54/0.57  fof(f81,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f9])).
% 1.54/0.57  fof(f9,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.54/0.57  fof(f135,plain,(
% 1.54/0.57    spl2_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f58,f132])).
% 1.54/0.57  fof(f58,plain,(
% 1.54/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.57    inference(cnf_transformation,[],[f48])).
% 1.54/0.57  fof(f130,plain,(
% 1.54/0.57    spl2_3),
% 1.54/0.57    inference(avatar_split_clause,[],[f57,f127])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    v3_funct_2(sK1,sK0,sK0)),
% 1.54/0.57    inference(cnf_transformation,[],[f48])).
% 1.54/0.57  fof(f125,plain,(
% 1.54/0.57    spl2_2),
% 1.54/0.57    inference(avatar_split_clause,[],[f56,f122])).
% 1.54/0.57  fof(f56,plain,(
% 1.54/0.57    v1_funct_2(sK1,sK0,sK0)),
% 1.54/0.57    inference(cnf_transformation,[],[f48])).
% 1.54/0.57  fof(f120,plain,(
% 1.54/0.57    spl2_1),
% 1.54/0.57    inference(avatar_split_clause,[],[f55,f117])).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    v1_funct_1(sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f48])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (14258)------------------------------
% 1.54/0.57  % (14258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (14258)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (14258)Memory used [KB]: 11257
% 1.54/0.57  % (14258)Time elapsed: 0.161 s
% 1.54/0.57  % (14258)------------------------------
% 1.54/0.57  % (14258)------------------------------
% 1.54/0.57  % (14237)Success in time 0.221 s
%------------------------------------------------------------------------------
