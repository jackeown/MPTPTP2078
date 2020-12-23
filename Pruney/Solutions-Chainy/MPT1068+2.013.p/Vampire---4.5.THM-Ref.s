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
% DateTime   : Thu Dec  3 13:07:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 280 expanded)
%              Number of leaves         :   36 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  532 (1070 expanded)
%              Number of equality atoms :  102 ( 198 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f86,f90,f95,f102,f106,f109,f113,f144,f149,f153,f161,f181,f189,f213,f245,f266,f331,f391,f408,f411,f527])).

fof(f527,plain,(
    spl7_30 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl7_30 ),
    inference(subsumption_resolution,[],[f525,f244])).

fof(f244,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_30 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl7_30
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f525,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f522,f61])).

% (31205)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f522,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(resolution,[],[f517,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f517,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(resolution,[],[f53,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f411,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_13
    | spl7_15
    | ~ spl7_33
    | ~ spl7_54 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_13
    | spl7_15
    | ~ spl7_33
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f409,f352])).

fof(f352,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_33 ),
    inference(resolution,[],[f293,f98])).

fof(f98,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_7
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f292,f75])).

fof(f75,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_funct_1(sK3)
        | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f291,f148])).

fof(f148,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_33 ),
    inference(superposition,[],[f123,f257])).

fof(f257,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl7_33
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1)) )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f81,f116])).

fof(f116,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_9 ),
    inference(resolution,[],[f105,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f105,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f71,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f71,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f409,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl7_15
    | ~ spl7_54 ),
    inference(superposition,[],[f160,f407])).

fof(f407,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl7_54
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f160,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl7_15
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f408,plain,
    ( spl7_54
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_43
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f397,f389,f329,f151,f111,f93,f74,f406])).

fof(f93,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f111,plain,
    ( spl7_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f151,plain,
    ( spl7_14
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f329,plain,
    ( spl7_43
  <=> k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f389,plain,
    ( spl7_51
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4))
        | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_2(X1,X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f397,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_43
    | ~ spl7_51 ),
    inference(forward_demodulation,[],[f396,f330])).

fof(f330,plain,
    ( k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f329])).

fof(f396,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f395,f94])).

fof(f94,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f395,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f394,f112])).

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f394,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f393,f75])).

fof(f393,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl7_14
    | ~ spl7_51 ),
    inference(resolution,[],[f390,f152])).

fof(f152,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f390,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4))
        | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_2(X1,X0,sK2) )
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f389])).

fof(f391,plain,
    ( spl7_25
    | spl7_51
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f196,f179,f104,f70,f389,f211])).

fof(f211,plain,
    ( spl7_25
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f179,plain,
    ( spl7_19
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4))
        | ~ v1_funct_2(X1,X0,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = sK2
        | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f195,f105])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4))
        | ~ v1_funct_2(X1,X0,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = sK2
        | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) )
    | ~ spl7_1
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f194,f71])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4))
        | ~ v1_funct_2(X1,X0,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = sK2
        | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) )
    | ~ spl7_19 ),
    inference(superposition,[],[f45,f180])).

fof(f180,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

fof(f331,plain,
    ( spl7_43
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f315,f111,f104,f74,f70,f329])).

fof(f315,plain,
    ( k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f313,f71])).

fof(f313,plain,
    ( ~ v1_funct_1(sK4)
    | k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(resolution,[],[f139,f105])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | k1_partfun1(sK1,sK2,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) )
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f132,f75])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_partfun1(sK1,sK2,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) )
    | ~ spl7_10 ),
    inference(resolution,[],[f112,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f266,plain,
    ( spl7_33
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f258,f208,f187,f256])).

fof(f187,plain,
    ( spl7_21
  <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f208,plain,
    ( spl7_24
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f258,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(superposition,[],[f209,f188])).

fof(f188,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f209,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f245,plain,
    ( ~ spl7_30
    | spl7_3
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f220,f211,f78,f243])).

fof(f78,plain,
    ( spl7_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f220,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_3
    | ~ spl7_25 ),
    inference(superposition,[],[f79,f212])).

fof(f212,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f211])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f213,plain,
    ( spl7_24
    | spl7_25
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f140,f111,f93,f211,f208])).

fof(f140,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f135,f94])).

fof(f135,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f112,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f189,plain,
    ( spl7_21
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f133,f111,f187])).

fof(f133,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(resolution,[],[f112,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f181,plain,
    ( spl7_19
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f118,f104,f179])).

fof(f118,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl7_9 ),
    inference(resolution,[],[f105,f57])).

fof(f161,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f37,f159])).

fof(f37,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f153,plain,
    ( spl7_14
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f145,f142,f104,f151])).

fof(f142,plain,
    ( spl7_12
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f145,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f143,f118])).

fof(f143,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f149,plain,
    ( spl7_13
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f131,f111,f147])).

fof(f131,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(resolution,[],[f112,f63])).

fof(f144,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f35,f142])).

fof(f35,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f113,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f42,f111])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,
    ( spl7_5
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl7_5
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f107,f89])).

fof(f89,plain,
    ( k1_xboole_0 != sK1
    | spl7_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_8 ),
    inference(resolution,[],[f101,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f101,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f106,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f39,f104])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,
    ( spl7_7
    | spl7_8
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f91,f84,f100,f97])).

fof(f84,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f91,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f85,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f85,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f95,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f36,f88])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f43,f78])).

fof(f43,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f40,f74])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f38,f70])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (31202)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (31215)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (31202)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (31216)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (31208)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f528,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f72,f76,f80,f86,f90,f95,f102,f106,f109,f113,f144,f149,f153,f161,f181,f189,f213,f245,f266,f331,f391,f408,f411,f527])).
% 0.21/0.48  fof(f527,plain,(
% 0.21/0.48    spl7_30),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f526])).
% 0.21/0.48  fof(f526,plain,(
% 0.21/0.48    $false | spl7_30),
% 0.21/0.48    inference(subsumption_resolution,[],[f525,f244])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | spl7_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f243])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    spl7_30 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.48  fof(f525,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f522,f61])).
% 0.21/0.48  % (31205)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f522,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f517,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f517,plain,(
% 0.21/0.48    ( ! [X18] : (r1_tarski(k1_xboole_0,X18)) )),
% 0.21/0.48    inference(resolution,[],[f53,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    ~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_9 | ~spl7_13 | spl7_15 | ~spl7_33 | ~spl7_54),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    $false | (~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_9 | ~spl7_13 | spl7_15 | ~spl7_33 | ~spl7_54)),
% 0.21/0.48    inference(subsumption_resolution,[],[f409,f352])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) | (~spl7_1 | ~spl7_2 | ~spl7_7 | ~spl7_9 | ~spl7_13 | ~spl7_33)),
% 0.21/0.48    inference(resolution,[],[f293,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    r2_hidden(sK5,sK1) | ~spl7_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl7_7 <=> r2_hidden(sK5,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl7_1 | ~spl7_2 | ~spl7_9 | ~spl7_13 | ~spl7_33)),
% 0.21/0.48    inference(subsumption_resolution,[],[f292,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl7_2 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_funct_1(sK3) | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl7_1 | ~spl7_9 | ~spl7_13 | ~spl7_33)),
% 0.21/0.48    inference(subsumption_resolution,[],[f291,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl7_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl7_13 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl7_1 | ~spl7_9 | ~spl7_33)),
% 0.21/0.48    inference(superposition,[],[f123,f257])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | ~spl7_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f256])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    spl7_33 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1))) ) | (~spl7_1 | ~spl7_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    v1_relat_1(sK4) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f105,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl7_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl7_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(sK4) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(k5_relat_1(X0,sK4),X1) = k1_funct_1(sK4,k1_funct_1(X0,X1))) ) | ~spl7_1),
% 0.21/0.48    inference(resolution,[],[f71,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    v1_funct_1(sK4) | ~spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl7_1 <=> v1_funct_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f409,plain,(
% 0.21/0.48    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | (spl7_15 | ~spl7_54)),
% 0.21/0.48    inference(superposition,[],[f160,f407])).
% 0.21/0.48  fof(f407,plain,(
% 0.21/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl7_54),
% 0.21/0.48    inference(avatar_component_clause,[],[f406])).
% 0.21/0.48  fof(f406,plain,(
% 0.21/0.48    spl7_54 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl7_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f159])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl7_15 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.48  fof(f408,plain,(
% 0.21/0.48    spl7_54 | ~spl7_2 | ~spl7_6 | ~spl7_10 | ~spl7_14 | ~spl7_43 | ~spl7_51),
% 0.21/0.48    inference(avatar_split_clause,[],[f397,f389,f329,f151,f111,f93,f74,f406])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl7_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl7_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl7_14 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    spl7_43 <=> k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    spl7_51 <=> ! [X1,X0] : (~r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(X1,X0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 0.21/0.48  fof(f397,plain,(
% 0.21/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl7_2 | ~spl7_6 | ~spl7_10 | ~spl7_14 | ~spl7_43 | ~spl7_51)),
% 0.21/0.48    inference(forward_demodulation,[],[f396,f330])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~spl7_43),
% 0.21/0.48    inference(avatar_component_clause,[],[f329])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl7_2 | ~spl7_6 | ~spl7_10 | ~spl7_14 | ~spl7_51)),
% 0.21/0.48    inference(subsumption_resolution,[],[f395,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK2) | ~spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f395,plain,(
% 0.21/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~v1_funct_2(sK3,sK1,sK2) | (~spl7_2 | ~spl7_10 | ~spl7_14 | ~spl7_51)),
% 0.21/0.48    inference(subsumption_resolution,[],[f394,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f111])).
% 0.21/0.48  fof(f394,plain,(
% 0.21/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | (~spl7_2 | ~spl7_14 | ~spl7_51)),
% 0.21/0.48    inference(subsumption_resolution,[],[f393,f75])).
% 0.21/0.48  fof(f393,plain,(
% 0.21/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | (~spl7_14 | ~spl7_51)),
% 0.21/0.48    inference(resolution,[],[f390,f152])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl7_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f151])).
% 0.21/0.48  fof(f390,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(X1,X0,sK2)) ) | ~spl7_51),
% 0.21/0.48    inference(avatar_component_clause,[],[f389])).
% 0.21/0.48  fof(f391,plain,(
% 0.21/0.48    spl7_25 | spl7_51 | ~spl7_1 | ~spl7_9 | ~spl7_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f196,f179,f104,f70,f389,f211])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    spl7_25 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    spl7_19 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) | ~v1_funct_2(X1,X0,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(X1) | k1_xboole_0 = sK2 | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4)) ) | (~spl7_1 | ~spl7_9 | ~spl7_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f195,f105])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) | ~v1_funct_2(X1,X0,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(X1) | k1_xboole_0 = sK2 | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4)) ) | (~spl7_1 | ~spl7_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f194,f71])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) | ~v1_funct_2(X1,X0,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(X1) | k1_xboole_0 = sK2 | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4)) ) | ~spl7_19),
% 0.21/0.48    inference(superposition,[],[f45,f180])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl7_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f179])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    spl7_43 | ~spl7_1 | ~spl7_2 | ~spl7_9 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f315,f111,f104,f74,f70,f329])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl7_1 | ~spl7_2 | ~spl7_9 | ~spl7_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f313,f71])).
% 0.21/0.48  fof(f313,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl7_2 | ~spl7_9 | ~spl7_10)),
% 0.21/0.48    inference(resolution,[],[f139,f105])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK1,sK2,X1,X2,sK3,X0) = k5_relat_1(sK3,X0)) ) | (~spl7_2 | ~spl7_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f132,f75])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_partfun1(sK1,sK2,X1,X2,sK3,X0) = k5_relat_1(sK3,X0)) ) | ~spl7_10),
% 0.21/0.48    inference(resolution,[],[f112,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    spl7_33 | ~spl7_21 | ~spl7_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f258,f208,f187,f256])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    spl7_21 <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    spl7_24 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | (~spl7_21 | ~spl7_24)),
% 0.21/0.48    inference(superposition,[],[f209,f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl7_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f187])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl7_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f208])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ~spl7_30 | spl7_3 | ~spl7_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f220,f211,f78,f243])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl7_3 <=> v1_xboole_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | (spl7_3 | ~spl7_25)),
% 0.21/0.48    inference(superposition,[],[f79,f212])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl7_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f211])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~v1_xboole_0(sK2) | spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl7_24 | spl7_25 | ~spl7_6 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f140,f111,f93,f211,f208])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl7_6 | ~spl7_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f94])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~spl7_10),
% 0.21/0.48    inference(resolution,[],[f112,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    spl7_21 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f133,f111,f187])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl7_10),
% 0.21/0.48    inference(resolution,[],[f112,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl7_19 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f118,f104,f179])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f105,f57])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ~spl7_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f159])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f14])).
% 0.21/0.48  fof(f14,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    spl7_14 | ~spl7_9 | ~spl7_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f145,f142,f104,f151])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl7_12 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl7_9 | ~spl7_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f143,f118])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl7_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f142])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl7_13 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f131,f111,f147])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl7_10),
% 0.21/0.48    inference(resolution,[],[f112,f63])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl7_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f142])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f111])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl7_5 | ~spl7_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    $false | (spl7_5 | ~spl7_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f107,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl7_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl7_5 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl7_8),
% 0.21/0.48    inference(resolution,[],[f101,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~spl7_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl7_8 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f104])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl7_7 | spl7_8 | ~spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f91,f84,f100,f97])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl7_4 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | r2_hidden(sK5,sK1) | ~spl7_4),
% 0.21/0.48    inference(resolution,[],[f85,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    m1_subset_1(sK5,sK1) | ~spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f93])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ~spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f88])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f84])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    m1_subset_1(sK5,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ~spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f78])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~v1_xboole_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f74])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl7_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f70])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_funct_1(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31202)------------------------------
% 0.21/0.48  % (31202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31202)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31202)Memory used [KB]: 6524
% 0.21/0.48  % (31202)Time elapsed: 0.065 s
% 0.21/0.48  % (31202)------------------------------
% 0.21/0.48  % (31202)------------------------------
% 0.21/0.49  % (31201)Success in time 0.126 s
%------------------------------------------------------------------------------
