%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 190 expanded)
%              Number of leaves         :   28 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  403 ( 787 expanded)
%              Number of equality atoms :   84 ( 177 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f91,f95,f109,f112,f118,f131,f137,f144,f165,f172,f183,f194])).

fof(f194,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f192,f181,f127,f85,f81])).

fof(f81,plain,
    ( spl7_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f85,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f127,plain,
    ( spl7_13
  <=> sK0 = k1_relset_1(sK0,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f181,plain,
    ( spl7_23
  <=> ! [X1] : ~ r2_hidden(k4_tarski(sK2,X1),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f192,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_23 ),
    inference(resolution,[],[f190,f182])).

fof(f182,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(sK2,X1),sK4)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f190,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK5(sK4,X0)),sK4)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,sK5(sK4,X0)),sK4) )
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f188,f128])).

fof(f128,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK4)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK0 != k1_relset_1(sK0,sK1,sK4)
        | r2_hidden(k4_tarski(X0,sK5(sK4,X0)),sK4) )
    | ~ spl7_5 ),
    inference(resolution,[],[f53,f86])).

fof(f86,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
            & r2_hidden(sK6(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f30,f29])).

% (9421)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (9436)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f29,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
        & r2_hidden(sK6(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f183,plain,
    ( ~ spl7_8
    | ~ spl7_7
    | spl7_23
    | spl7_21 ),
    inference(avatar_split_clause,[],[f174,f169,f181,f93,f98])).

fof(f98,plain,
    ( spl7_8
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f93,plain,
    ( spl7_7
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f169,plain,
    ( spl7_21
  <=> r2_hidden(sK2,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f174,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(sK2,X1),sK4)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | spl7_21 ),
    inference(resolution,[],[f170,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f170,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK4))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f169])).

fof(f172,plain,
    ( ~ spl7_21
    | ~ spl7_3
    | spl7_15
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f167,f163,f142,f77,f169])).

fof(f77,plain,
    ( spl7_3
  <=> r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f142,plain,
    ( spl7_15
  <=> r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f163,plain,
    ( spl7_20
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k1_funct_1(sK4,X0),X1)
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f167,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    | ~ r2_hidden(sK2,k1_relat_1(sK4))
    | spl7_15
    | ~ spl7_20 ),
    inference(resolution,[],[f164,f143])).

fof(f143,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | ~ r2_hidden(k1_funct_1(sK4,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK4)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( ~ spl7_8
    | spl7_20
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f161,f93,f163,f98])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK4,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | ~ v1_relat_1(sK4) )
    | ~ spl7_7 ),
    inference(resolution,[],[f60,f94])).

fof(f94,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(f144,plain,
    ( ~ spl7_15
    | spl7_11
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f140,f135,f116,f142])).

fof(f116,plain,
    ( spl7_11
  <=> k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f135,plain,
    ( spl7_14
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f140,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    | spl7_11
    | ~ spl7_14 ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2)
    | ~ r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    | spl7_11
    | ~ spl7_14 ),
    inference(superposition,[],[f117,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0)
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f117,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f137,plain,
    ( ~ spl7_8
    | spl7_14
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f133,f93,f135,f98])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0)
        | ~ v1_relat_1(sK4) )
    | ~ spl7_7 ),
    inference(resolution,[],[f54,f94])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

fof(f131,plain,
    ( spl7_13
    | spl7_2
    | ~ spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f125,f85,f89,f73,f127])).

fof(f73,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f89,plain,
    ( spl7_6
  <=> v1_funct_2(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f125,plain,
    ( ~ v1_funct_2(sK4,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK4)
    | ~ spl7_5 ),
    inference(resolution,[],[f45,f86])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f118,plain,
    ( ~ spl7_11
    | spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f114,f85,f69,f116])).

fof(f69,plain,
    ( spl7_1
  <=> k1_funct_1(sK4,sK2) = k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f114,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | spl7_1
    | ~ spl7_5 ),
    inference(superposition,[],[f70,f113])).

fof(f113,plain,
    ( ! [X0] : k6_relset_1(sK0,sK1,X0,sK4) = k8_relat_1(X0,sK4)
    | ~ spl7_5 ),
    inference(resolution,[],[f61,f86])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f70,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f112,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f108,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f108,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_10
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f109,plain,
    ( ~ spl7_10
    | ~ spl7_5
    | spl7_8 ),
    inference(avatar_split_clause,[],[f105,f98,f85,f107])).

fof(f105,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_5
    | spl7_8 ),
    inference(resolution,[],[f104,f86])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_8 ),
    inference(resolution,[],[f99,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f99,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f95,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    & k1_xboole_0 != sK1
    & r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK4,sK0,sK1)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
        & k1_xboole_0 != X1
        & r2_hidden(k1_funct_1(X4,X2),X3)
        & r2_hidden(X2,X0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
      & k1_xboole_0 != sK1
      & r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK4,sK0,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
            & r2_hidden(X2,X0) )
         => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
          & r2_hidden(X2,X0) )
       => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_funct_2)).

fof(f91,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    v1_funct_2(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f42,f69])).

fof(f42,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f25])).

% (9420)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (9429)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (9429)Refutation not found, incomplete strategy% (9429)------------------------------
% 0.21/0.47  % (9429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9430)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (9422)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (9429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9429)Memory used [KB]: 1663
% 0.21/0.49  % (9429)Time elapsed: 0.007 s
% 0.21/0.49  % (9429)------------------------------
% 0.21/0.49  % (9429)------------------------------
% 0.21/0.49  % (9422)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f91,f95,f109,f112,f118,f131,f137,f144,f165,f172,f183,f194])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ~spl7_4 | ~spl7_5 | ~spl7_13 | ~spl7_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f192,f181,f127,f85,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl7_4 <=> r2_hidden(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl7_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl7_13 <=> sK0 = k1_relset_1(sK0,sK1,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    spl7_23 <=> ! [X1] : ~r2_hidden(k4_tarski(sK2,X1),sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ~r2_hidden(sK2,sK0) | (~spl7_5 | ~spl7_13 | ~spl7_23)),
% 0.21/0.49    inference(resolution,[],[f190,f182])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(k4_tarski(sK2,X1),sK4)) ) | ~spl7_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f181])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK4,X0)),sK4) | ~r2_hidden(X0,sK0)) ) | (~spl7_5 | ~spl7_13)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ( ! [X0] : (sK0 != sK0 | ~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,sK5(sK4,X0)),sK4)) ) | (~spl7_5 | ~spl7_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f188,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK4) | ~spl7_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | sK0 != k1_relset_1(sK0,sK1,sK4) | r2_hidden(k4_tarski(X0,sK5(sK4,X0)),sK4)) ) | ~spl7_5),
% 0.21/0.49    inference(resolution,[],[f53,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f30,f29])).
% 0.21/0.50  % (9421)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (9436)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    inference(rectify,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~spl7_8 | ~spl7_7 | spl7_23 | spl7_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f174,f169,f181,f93,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl7_8 <=> v1_relat_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl7_7 <=> v1_funct_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl7_21 <=> r2_hidden(sK2,k1_relat_1(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(k4_tarski(sK2,X1),sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | spl7_21),
% 0.21/0.51    inference(resolution,[],[f170,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~r2_hidden(sK2,k1_relat_1(sK4)) | spl7_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~spl7_21 | ~spl7_3 | spl7_15 | ~spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f167,f163,f142,f77,f169])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl7_3 <=> r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl7_15 <=> r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl7_20 <=> ! [X1,X0] : (~r2_hidden(k1_funct_1(sK4,X0),X1) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) | ~r2_hidden(X0,k1_relat_1(sK4)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) | ~r2_hidden(sK2,k1_relat_1(sK4)) | (spl7_15 | ~spl7_20)),
% 0.21/0.51    inference(resolution,[],[f164,f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) | spl7_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) | ~r2_hidden(k1_funct_1(sK4,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK4))) ) | ~spl7_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f163])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~spl7_8 | spl7_20 | ~spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f161,f93,f163,f98])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(sK4,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK4)) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) | ~v1_relat_1(sK4)) ) | ~spl7_7),
% 0.21/0.51    inference(resolution,[],[f60,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    v1_funct_1(sK4) | ~spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~spl7_15 | spl7_11 | ~spl7_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f140,f135,f116,f142])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl7_11 <=> k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl7_14 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ~r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) | (spl7_11 | ~spl7_14)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) | ~r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) | (spl7_11 | ~spl7_14)),
% 0.21/0.51    inference(superposition,[],[f117,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))) ) | ~spl7_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f135])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) | spl7_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ~spl7_8 | spl7_14 | ~spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f133,f93,f135,f98])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) | ~v1_relat_1(sK4)) ) | ~spl7_7),
% 0.21/0.51    inference(resolution,[],[f54,f94])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl7_13 | spl7_2 | ~spl7_6 | ~spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f125,f85,f89,f73,f127])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl7_6 <=> v1_funct_2(sK4,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~v1_funct_2(sK4,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK4) | ~spl7_5),
% 0.21/0.51    inference(resolution,[],[f45,f86])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ~spl7_11 | spl7_1 | ~spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f114,f85,f69,f116])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl7_1 <=> k1_funct_1(sK4,sK2) = k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) | (spl7_1 | ~spl7_5)),
% 0.21/0.51    inference(superposition,[],[f70,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X0] : (k6_relset_1(sK0,sK1,X0,sK4) = k8_relat_1(X0,sK4)) ) | ~spl7_5),
% 0.21/0.51    inference(resolution,[],[f61,f86])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) | spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f69])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl7_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    $false | spl7_10),
% 0.21/0.51    inference(resolution,[],[f108,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl7_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl7_10 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ~spl7_10 | ~spl7_5 | spl7_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f105,f98,f85,f107])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_5 | spl7_8)),
% 0.21/0.51    inference(resolution,[],[f104,f86])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_8),
% 0.21/0.51    inference(resolution,[],[f99,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~v1_relat_1(sK4) | spl7_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f98])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f93])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) & k1_xboole_0 != sK1 & r2_hidden(k1_funct_1(sK4,sK2),sK3) & r2_hidden(sK2,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK4,sK0,sK1) & v1_funct_1(sK4)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1 & r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) & k1_xboole_0 != sK1 & r2_hidden(k1_funct_1(sK4,sK2),sK3) & r2_hidden(sK2,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK4,sK0,sK1) & v1_funct_1(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1 & r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (((k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1) & (r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ((r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0)) => (k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) | k1_xboole_0 = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ((r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0)) => (k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) | k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_funct_2)).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl7_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f89])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    v1_funct_2(sK4,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f85])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f81])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    r2_hidden(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f77])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ~spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f73])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ~spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f69])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  % (9420)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (9428)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (9422)------------------------------
% 0.21/0.51  % (9422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9422)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (9422)Memory used [KB]: 10746
% 0.21/0.51  % (9422)Time elapsed: 0.034 s
% 0.21/0.51  % (9422)------------------------------
% 0.21/0.51  % (9422)------------------------------
% 0.21/0.51  % (9414)Success in time 0.145 s
%------------------------------------------------------------------------------
