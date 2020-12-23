%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 170 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  278 ( 463 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f73,f77,f87,f94,f98,f105,f124,f141,f149,f161,f168,f181])).

fof(f181,plain,
    ( ~ spl5_19
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f179,f160])).

fof(f160,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl5_19
  <=> sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f179,plain,
    ( sK0 != k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ spl5_20 ),
    inference(resolution,[],[f167,f27])).

fof(f27,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | sK0 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f167,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_20
  <=> m1_subset_1(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f168,plain,
    ( spl5_20
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f162,f139,f92,f166])).

fof(f92,plain,
    ( spl5_8
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f139,plain,
    ( spl5_17
  <=> r2_hidden(sK4(sK0,sK1,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f162,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(resolution,[],[f143,f93])).

fof(f93,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))
        | m1_subset_1(sK4(sK0,sK1,sK3),X0) )
    | ~ spl5_17 ),
    inference(resolution,[],[f140,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f140,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),k1_relat_1(sK3))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f161,plain,
    ( spl5_19
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f157,f147,f71,f51,f159])).

fof(f51,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,
    ( spl5_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f147,plain,
    ( spl5_18
  <=> r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f157,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f156,f72])).

fof(f72,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f71])).

% (22975)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f156,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f152,f52])).

fof(f52,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f152,plain,
    ( ~ v1_funct_1(sK3)
    | sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_18 ),
    inference(resolution,[],[f148,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f148,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl5_18
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f131,f122,f71,f147])).

fof(f122,plain,
    ( spl5_15
  <=> r2_hidden(sK0,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f131,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3)
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f127,f72])).

fof(f127,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_15 ),
    inference(resolution,[],[f123,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f123,plain,
    ( r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f141,plain,
    ( spl5_17
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f130,f122,f71,f139])).

fof(f130,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),k1_relat_1(sK3))
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f126,f72])).

fof(f126,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_15 ),
    inference(resolution,[],[f123,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f124,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f116,f103,f59,f122])).

fof(f59,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f103,plain,
    ( spl5_10
  <=> k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f116,plain,
    ( r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(superposition,[],[f60,f104])).

fof(f104,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f60,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f105,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f99,f96,f55,f103])).

fof(f55,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f96,plain,
    ( spl5_9
  <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f99,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f97,f65])).

fof(f65,plain,
    ( ! [X0] : k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f97,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f63,f55,f96])).

fof(f63,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f94,plain,
    ( spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f90,f85,f92])).

fof(f85,plain,
    ( spl5_7
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f90,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_7 ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f86,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,
    ( spl5_7
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f79,f75,f71,f85])).

fof(f75,plain,
    ( spl5_5
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f79,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f78,f72])).

fof(f78,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f76,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f62,f55,f75])).

fof(f62,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f73,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f68,f55,f71])).

fof(f68,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f67,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f61,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:18:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (22969)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (22966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (22977)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (22961)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (22962)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (22967)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (22971)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (22961)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (22980)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f53,f57,f61,f73,f77,f87,f94,f98,f105,f124,f141,f149,f161,f168,f181])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ~spl5_19 | ~spl5_20),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    $false | (~spl5_19 | ~spl5_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f179,f160])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~spl5_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl5_19 <=> sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    sK0 != k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~spl5_20),
% 0.21/0.52    inference(resolution,[],[f167,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    m1_subset_1(sK4(sK0,sK1,sK3),sK1) | ~spl5_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl5_20 <=> m1_subset_1(sK4(sK0,sK1,sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    spl5_20 | ~spl5_8 | ~spl5_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f162,f139,f92,f166])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl5_8 <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl5_17 <=> r2_hidden(sK4(sK0,sK1,sK3),k1_relat_1(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    m1_subset_1(sK4(sK0,sK1,sK3),sK1) | (~spl5_8 | ~spl5_17)),
% 0.21/0.52    inference(resolution,[],[f143,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) | m1_subset_1(sK4(sK0,sK1,sK3),X0)) ) | ~spl5_17),
% 0.21/0.52    inference(resolution,[],[f140,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    r2_hidden(sK4(sK0,sK1,sK3),k1_relat_1(sK3)) | ~spl5_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f139])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    spl5_19 | ~spl5_1 | ~spl5_4 | ~spl5_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f157,f147,f71,f51,f159])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl5_4 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    spl5_18 <=> r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | (~spl5_1 | ~spl5_4 | ~spl5_18)),
% 0.21/0.52    inference(subsumption_resolution,[],[f156,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  % (22975)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~v1_relat_1(sK3) | (~spl5_1 | ~spl5_18)),
% 0.21/0.52    inference(subsumption_resolution,[],[f152,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    v1_funct_1(sK3) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~v1_relat_1(sK3) | ~spl5_18),
% 0.21/0.52    inference(resolution,[],[f148,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3) | ~spl5_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f147])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl5_18 | ~spl5_4 | ~spl5_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f122,f71,f147])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl5_15 <=> r2_hidden(sK0,k9_relat_1(sK3,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3) | (~spl5_4 | ~spl5_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f127,f72])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3) | ~v1_relat_1(sK3) | ~spl5_15),
% 0.21/0.52    inference(resolution,[],[f123,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    r2_hidden(sK0,k9_relat_1(sK3,sK1)) | ~spl5_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    spl5_17 | ~spl5_4 | ~spl5_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f130,f122,f71,f139])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    r2_hidden(sK4(sK0,sK1,sK3),k1_relat_1(sK3)) | (~spl5_4 | ~spl5_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f126,f72])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    r2_hidden(sK4(sK0,sK1,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl5_15),
% 0.21/0.52    inference(resolution,[],[f123,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl5_15 | ~spl5_3 | ~spl5_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f116,f103,f59,f122])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl5_3 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl5_10 <=> k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    r2_hidden(sK0,k9_relat_1(sK3,sK1)) | (~spl5_3 | ~spl5_10)),
% 0.21/0.52    inference(superposition,[],[f60,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl5_10 | ~spl5_2 | ~spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f99,f96,f55,f103])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl5_9 <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | (~spl5_2 | ~spl5_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f97,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f56,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f55])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl5_9 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f63,f55,f96])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f56,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl5_8 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f90,f85,f92])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl5_7 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f86,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK3),sK1) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl5_7 | ~spl5_4 | ~spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f79,f75,f71,f85])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl5_5 <=> v4_relat_1(sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK3),sK1) | (~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f72])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl5_5),
% 0.21/0.52    inference(resolution,[],[f76,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    v4_relat_1(sK3,sK1) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl5_5 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f62,f55,f75])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    v4_relat_1(sK3,sK1) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f56,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl5_4 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f68,f55,f71])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl5_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f67,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f56,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f59])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f55])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f51])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22961)------------------------------
% 0.21/0.52  % (22961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22961)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22961)Memory used [KB]: 6268
% 0.21/0.52  % (22961)Time elapsed: 0.082 s
% 0.21/0.52  % (22961)------------------------------
% 0.21/0.52  % (22961)------------------------------
% 0.21/0.53  % (22960)Success in time 0.163 s
%------------------------------------------------------------------------------
