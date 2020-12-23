%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 379 expanded)
%              Number of leaves         :   52 ( 178 expanded)
%              Depth                    :    8
%              Number of atoms          :  670 (1871 expanded)
%              Number of equality atoms :  107 ( 370 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f129,f155,f165,f174,f177,f185,f189,f202,f210,f223,f232,f234,f243,f253,f284,f285,f301,f314,f318,f348,f361,f365])).

fof(f365,plain,
    ( ~ spl7_23
    | ~ spl7_4
    | ~ spl7_43
    | spl7_48 ),
    inference(avatar_split_clause,[],[f362,f359,f312,f97,f200])).

fof(f200,plain,
    ( spl7_23
  <=> v5_relat_1(sK3,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f97,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f312,plain,
    ( spl7_43
  <=> ! [X1,X2] :
        ( r2_hidden(k1_funct_1(sK3,X1),X2)
        | ~ m1_subset_1(X1,sK1)
        | ~ v5_relat_1(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f359,plain,
    ( spl7_48
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f362,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ spl7_4
    | ~ spl7_43
    | spl7_48 ),
    inference(resolution,[],[f360,f350])).

fof(f350,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,sK5),X0)
        | ~ v5_relat_1(sK3,X0) )
    | ~ spl7_4
    | ~ spl7_43 ),
    inference(resolution,[],[f313,f98])).

fof(f98,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f313,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,sK1)
        | r2_hidden(k1_funct_1(sK3,X1),X2)
        | ~ v5_relat_1(sK3,X2) )
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f312])).

fof(f360,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl7_48 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,
    ( ~ spl7_29
    | ~ spl7_30
    | ~ spl7_6
    | ~ spl7_48
    | spl7_47 ),
    inference(avatar_split_clause,[],[f356,f345,f359,f105,f241,f238])).

fof(f238,plain,
    ( spl7_29
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f241,plain,
    ( spl7_30
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f105,plain,
    ( spl7_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f345,plain,
    ( spl7_47
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f356,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl7_47 ),
    inference(trivial_inequality_removal,[],[f355])).

fof(f355,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl7_47 ),
    inference(superposition,[],[f346,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f346,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl7_47 ),
    inference(avatar_component_clause,[],[f345])).

fof(f348,plain,
    ( spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | spl7_2
    | ~ spl7_47
    | ~ spl7_24
    | spl7_1
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f337,f183,f153,f85,f204,f345,f89,f97,f101,f105,f109,f113,f117,f121])).

fof(f121,plain,
    ( spl7_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f117,plain,
    ( spl7_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f113,plain,
    ( spl7_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f109,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f101,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f89,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f204,plain,
    ( spl7_24
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f85,plain,
    ( spl7_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f153,plain,
    ( spl7_15
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f183,plain,
    ( spl7_20
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f337,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | spl7_1
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f336,f154])).

fof(f154,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f336,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | spl7_1
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f335,f184])).

fof(f184,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f183])).

fof(f335,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | spl7_1 ),
    inference(superposition,[],[f86,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f86,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f318,plain,
    ( spl7_2
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f316,f305,f89])).

fof(f305,plain,
    ( spl7_41
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f316,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_41 ),
    inference(resolution,[],[f306,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f306,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f305])).

fof(f314,plain,
    ( spl7_41
    | spl7_43
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f303,f299,f312,f305])).

fof(f299,plain,
    ( spl7_40
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,sK1)
        | r2_hidden(k1_funct_1(sK3,X4),X5)
        | ~ v5_relat_1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f303,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k1_funct_1(sK3,X1),X2)
        | ~ v5_relat_1(sK3,X2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_40 ),
    inference(resolution,[],[f300,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f300,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK1)
        | r2_hidden(k1_funct_1(sK3,X4),X5)
        | ~ v5_relat_1(sK3,X5) )
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f299])).

fof(f301,plain,
    ( spl7_27
    | spl7_40
    | ~ spl7_9
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f297,f282,f117,f299,f225])).

fof(f225,plain,
    ( spl7_27
  <=> ! [X3,X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f282,plain,
    ( spl7_37
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f297,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(X4,sK1)
        | ~ v5_relat_1(sK3,X5)
        | r2_hidden(k1_funct_1(sK3,X4),X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl7_9
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f292,f283])).

fof(f283,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f282])).

fof(f292,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(X4,k1_relat_1(sK3))
        | ~ v5_relat_1(sK3,X5)
        | r2_hidden(k1_funct_1(sK3,X4),X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl7_9 ),
    inference(resolution,[],[f214,f118])).

fof(f118,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f214,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v5_relat_1(X1,X2)
      | r2_hidden(k1_funct_1(X1,X0),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f65,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r2_hidden(k1_funct_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (29833)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f285,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f284,plain,
    ( ~ spl7_7
    | spl7_36
    | spl7_37
    | ~ spl7_8
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f276,f187,f113,f282,f279,f109])).

fof(f279,plain,
    ( spl7_36
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f187,plain,
    ( spl7_21
  <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f276,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_8
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f275,f188])).

fof(f188,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f275,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_8 ),
    inference(resolution,[],[f73,f114])).

fof(f114,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f253,plain,
    ( ~ spl7_5
    | spl7_29 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl7_5
    | spl7_29 ),
    inference(subsumption_resolution,[],[f102,f251])).

fof(f251,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_29 ),
    inference(resolution,[],[f239,f69])).

fof(f239,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_29 ),
    inference(avatar_component_clause,[],[f238])).

fof(f102,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f243,plain,
    ( ~ spl7_29
    | spl7_30
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f235,f221,f241,f238])).

fof(f221,plain,
    ( spl7_26
  <=> r1_tarski(k2_relat_1(sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f235,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | ~ spl7_26 ),
    inference(resolution,[],[f222,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f222,plain,
    ( r1_tarski(k2_relat_1(sK4),sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f221])).

fof(f234,plain,
    ( ~ spl7_5
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f102,f219])).

fof(f219,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl7_25
  <=> ! [X1,X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f232,plain,
    ( ~ spl7_7
    | ~ spl7_27 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f110,f226])).

fof(f226,plain,
    ( ! [X2,X3] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f225])).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f223,plain,
    ( spl7_25
    | spl7_26
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f215,f101,f221,f218])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(sK4),sK0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_5 ),
    inference(resolution,[],[f145,f102])).

fof(f145,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | r1_tarski(k2_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f144,f69])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

% (29830)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f210,plain,
    ( spl7_24
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f209,f183,f153,f93,f204])).

fof(f93,plain,
    ( spl7_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f209,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f194,f154])).

fof(f194,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(superposition,[],[f94,f184])).

fof(f94,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f202,plain,
    ( spl7_23
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f191,f183,f172,f200])).

fof(f172,plain,
    ( spl7_19
  <=> v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f191,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(superposition,[],[f173,f184])).

fof(f173,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f189,plain,
    ( spl7_21
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f181,f109,f187])).

fof(f181,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f71,f110])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f185,plain,
    ( spl7_20
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f180,f101,f183])).

fof(f180,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl7_5 ),
    inference(resolution,[],[f71,f102])).

fof(f177,plain,
    ( ~ spl7_7
    | spl7_18 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl7_7
    | spl7_18 ),
    inference(subsumption_resolution,[],[f110,f175])).

fof(f175,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_18 ),
    inference(resolution,[],[f170,f69])).

fof(f170,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f174,plain,
    ( ~ spl7_18
    | spl7_19
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f166,f163,f172,f169])).

fof(f163,plain,
    ( spl7_17
  <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f166,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl7_17 ),
    inference(resolution,[],[f164,f63])).

fof(f164,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( spl7_17
    | ~ spl7_3
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f157,f153,f93,f163])).

fof(f157,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_3
    | ~ spl7_15 ),
    inference(superposition,[],[f94,f154])).

fof(f155,plain,
    ( spl7_15
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f147,f109,f153])).

fof(f147,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f70,f110])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f129,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f125,f127])).

fof(f127,plain,
    ( spl7_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f125,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f124,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK6(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f67,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

% (29825)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

% (29829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f123,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f48,f121])).

fof(f48,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f119,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f49,f117])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f115,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f50,f113])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f52,f105])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f54,f97])).

fof(f54,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f55,f93])).

fof(f55,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f56,f89])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f57,f85])).

fof(f57,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:51:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (29819)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (29820)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (29821)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (29822)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (29823)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (29831)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (29818)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (29824)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (29837)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (29817)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (29826)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (29832)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (29818)Refutation not found, incomplete strategy% (29818)------------------------------
% 0.22/0.51  % (29818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29818)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29818)Memory used [KB]: 10618
% 0.22/0.51  % (29818)Time elapsed: 0.059 s
% 0.22/0.51  % (29818)------------------------------
% 0.22/0.51  % (29818)------------------------------
% 0.22/0.51  % (29834)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (29828)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (29823)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f373,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f129,f155,f165,f174,f177,f185,f189,f202,f210,f223,f232,f234,f243,f253,f284,f285,f301,f314,f318,f348,f361,f365])).
% 0.22/0.51  fof(f365,plain,(
% 0.22/0.51    ~spl7_23 | ~spl7_4 | ~spl7_43 | spl7_48),
% 0.22/0.51    inference(avatar_split_clause,[],[f362,f359,f312,f97,f200])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    spl7_23 <=> v5_relat_1(sK3,k1_relat_1(sK4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl7_4 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    spl7_43 <=> ! [X1,X2] : (r2_hidden(k1_funct_1(sK3,X1),X2) | ~m1_subset_1(X1,sK1) | ~v5_relat_1(sK3,X2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    spl7_48 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 0.22/0.51  fof(f362,plain,(
% 0.22/0.51    ~v5_relat_1(sK3,k1_relat_1(sK4)) | (~spl7_4 | ~spl7_43 | spl7_48)),
% 0.22/0.51    inference(resolution,[],[f360,f350])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK5),X0) | ~v5_relat_1(sK3,X0)) ) | (~spl7_4 | ~spl7_43)),
% 0.22/0.51    inference(resolution,[],[f313,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    m1_subset_1(sK5,sK1) | ~spl7_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f97])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,sK1) | r2_hidden(k1_funct_1(sK3,X1),X2) | ~v5_relat_1(sK3,X2)) ) | ~spl7_43),
% 0.22/0.51    inference(avatar_component_clause,[],[f312])).
% 0.22/0.51  fof(f360,plain,(
% 0.22/0.51    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl7_48),
% 0.22/0.51    inference(avatar_component_clause,[],[f359])).
% 0.22/0.51  fof(f361,plain,(
% 0.22/0.51    ~spl7_29 | ~spl7_30 | ~spl7_6 | ~spl7_48 | spl7_47),
% 0.22/0.51    inference(avatar_split_clause,[],[f356,f345,f359,f105,f241,f238])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    spl7_29 <=> v1_relat_1(sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    spl7_30 <=> v5_relat_1(sK4,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    spl7_6 <=> v1_funct_1(sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    spl7_47 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl7_47),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f355])).
% 0.22/0.51  fof(f355,plain,(
% 0.22/0.51    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl7_47),
% 0.22/0.51    inference(superposition,[],[f346,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.22/0.51  fof(f346,plain,(
% 0.22/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl7_47),
% 0.22/0.51    inference(avatar_component_clause,[],[f345])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_7 | ~spl7_6 | ~spl7_5 | ~spl7_4 | spl7_2 | ~spl7_47 | ~spl7_24 | spl7_1 | ~spl7_15 | ~spl7_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f337,f183,f153,f85,f204,f345,f89,f97,f101,f105,f109,f113,f117,f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl7_10 <=> v1_xboole_0(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl7_9 <=> v1_funct_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl7_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl7_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    spl7_24 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl7_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    spl7_15 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    spl7_20 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2) | (spl7_1 | ~spl7_15 | ~spl7_20)),
% 0.22/0.51    inference(forward_demodulation,[],[f336,f154])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl7_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f153])).
% 0.22/0.51  fof(f336,plain,(
% 0.22/0.51    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2) | (spl7_1 | ~spl7_20)),
% 0.22/0.51    inference(forward_demodulation,[],[f335,f184])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl7_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f183])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2) | spl7_1),
% 0.22/0.51    inference(superposition,[],[f86,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl7_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    spl7_2 | ~spl7_41),
% 0.22/0.51    inference(avatar_split_clause,[],[f316,f305,f89])).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    spl7_41 <=> v1_xboole_0(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.22/0.51  fof(f316,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl7_41),
% 0.22/0.51    inference(resolution,[],[f306,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.51  fof(f306,plain,(
% 0.22/0.51    v1_xboole_0(sK1) | ~spl7_41),
% 0.22/0.51    inference(avatar_component_clause,[],[f305])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    spl7_41 | spl7_43 | ~spl7_40),
% 0.22/0.51    inference(avatar_split_clause,[],[f303,f299,f312,f305])).
% 0.22/0.51  fof(f299,plain,(
% 0.22/0.51    spl7_40 <=> ! [X5,X4] : (~r2_hidden(X4,sK1) | r2_hidden(k1_funct_1(sK3,X4),X5) | ~v5_relat_1(sK3,X5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    ( ! [X2,X1] : (r2_hidden(k1_funct_1(sK3,X1),X2) | ~v5_relat_1(sK3,X2) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1)) ) | ~spl7_40),
% 0.22/0.51    inference(resolution,[],[f300,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~r2_hidden(X4,sK1) | r2_hidden(k1_funct_1(sK3,X4),X5) | ~v5_relat_1(sK3,X5)) ) | ~spl7_40),
% 0.22/0.51    inference(avatar_component_clause,[],[f299])).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    spl7_27 | spl7_40 | ~spl7_9 | ~spl7_37),
% 0.22/0.51    inference(avatar_split_clause,[],[f297,f282,f117,f299,f225])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    spl7_27 <=> ! [X3,X2] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    spl7_37 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.51  fof(f297,plain,(
% 0.22/0.51    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,sK1) | ~v5_relat_1(sK3,X5) | r2_hidden(k1_funct_1(sK3,X4),X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | (~spl7_9 | ~spl7_37)),
% 0.22/0.51    inference(forward_demodulation,[],[f292,f283])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    sK1 = k1_relat_1(sK3) | ~spl7_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f282])).
% 0.22/0.51  fof(f292,plain,(
% 0.22/0.51    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k1_relat_1(sK3)) | ~v5_relat_1(sK3,X5) | r2_hidden(k1_funct_1(sK3,X4),X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl7_9),
% 0.22/0.51    inference(resolution,[],[f214,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    v1_funct_1(sK3) | ~spl7_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v5_relat_1(X1,X2) | r2_hidden(k1_funct_1(X1,X0),X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.51    inference(resolution,[],[f65,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | r2_hidden(k1_funct_1(X1,X2),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  % (29833)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    ~spl7_7 | spl7_36 | spl7_37 | ~spl7_8 | ~spl7_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f276,f187,f113,f282,f279,f109])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    spl7_36 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    spl7_21 <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl7_8 | ~spl7_21)),
% 0.22/0.51    inference(forward_demodulation,[],[f275,f188])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl7_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f187])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_8),
% 0.22/0.51    inference(resolution,[],[f73,f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK1,sK2) | ~spl7_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f113])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    ~spl7_5 | spl7_29),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f252])).
% 0.22/0.51  fof(f252,plain,(
% 0.22/0.51    $false | (~spl7_5 | spl7_29)),
% 0.22/0.51    inference(subsumption_resolution,[],[f102,f251])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_29),
% 0.22/0.51    inference(resolution,[],[f239,f69])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    ~v1_relat_1(sK4) | spl7_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f238])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl7_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f101])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    ~spl7_29 | spl7_30 | ~spl7_26),
% 0.22/0.51    inference(avatar_split_clause,[],[f235,f221,f241,f238])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl7_26 <=> r1_tarski(k2_relat_1(sK4),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | ~spl7_26),
% 0.22/0.51    inference(resolution,[],[f222,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK4),sK0) | ~spl7_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f221])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    ~spl7_5 | ~spl7_25),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f233])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    $false | (~spl7_5 | ~spl7_25)),
% 0.22/0.51    inference(subsumption_resolution,[],[f102,f219])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f218])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    spl7_25 <=> ! [X1,X0] : ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ~spl7_7 | ~spl7_27),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f231])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    $false | (~spl7_7 | ~spl7_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f110,f226])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl7_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f225])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f109])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    spl7_25 | spl7_26 | ~spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f215,f101,f221,f218])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(sK4),sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_5),
% 0.22/0.51    inference(resolution,[],[f145,f102])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r1_tarski(k2_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.51    inference(resolution,[],[f144,f69])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.51    inference(resolution,[],[f72,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  % (29830)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    spl7_24 | ~spl7_3 | ~spl7_15 | ~spl7_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f209,f183,f153,f93,f204])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl7_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl7_3 | ~spl7_15 | ~spl7_20)),
% 0.22/0.51    inference(forward_demodulation,[],[f194,f154])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl7_3 | ~spl7_20)),
% 0.22/0.51    inference(superposition,[],[f94,f184])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl7_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f93])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    spl7_23 | ~spl7_19 | ~spl7_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f191,f183,f172,f200])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    spl7_19 <=> v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    v5_relat_1(sK3,k1_relat_1(sK4)) | (~spl7_19 | ~spl7_20)),
% 0.22/0.51    inference(superposition,[],[f173,f184])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) | ~spl7_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f172])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    spl7_21 | ~spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f181,f109,f187])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl7_7),
% 0.22/0.51    inference(resolution,[],[f71,f110])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    spl7_20 | ~spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f180,f101,f183])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl7_5),
% 0.22/0.51    inference(resolution,[],[f71,f102])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ~spl7_7 | spl7_18),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f176])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    $false | (~spl7_7 | spl7_18)),
% 0.22/0.51    inference(subsumption_resolution,[],[f110,f175])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_18),
% 0.22/0.51    inference(resolution,[],[f170,f69])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ~v1_relat_1(sK3) | spl7_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f169])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    spl7_18 <=> v1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ~spl7_18 | spl7_19 | ~spl7_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f166,f163,f172,f169])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    spl7_17 <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) | ~v1_relat_1(sK3) | ~spl7_17),
% 0.22/0.51    inference(resolution,[],[f164,f63])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl7_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f163])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl7_17 | ~spl7_3 | ~spl7_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f157,f153,f93,f163])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | (~spl7_3 | ~spl7_15)),
% 0.22/0.51    inference(superposition,[],[f94,f154])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    spl7_15 | ~spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f147,f109,f153])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl7_7),
% 0.22/0.51    inference(resolution,[],[f70,f110])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl7_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f125,f127])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl7_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(resolution,[],[f124,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,sK6(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(resolution,[],[f67,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  % (29825)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(rectify,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  % (29829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ~spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f48,f121])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~v1_xboole_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f40,f39,f38,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f15])).
% 0.22/0.51  fof(f15,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl7_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f117])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl7_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f50,f113])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f51,f109])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f105])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f101])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl7_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f97])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    m1_subset_1(sK5,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f55,f93])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ~spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f89])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    k1_xboole_0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ~spl7_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f57,f85])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (29823)------------------------------
% 0.22/0.51  % (29823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29823)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (29823)Memory used [KB]: 10874
% 0.22/0.51  % (29823)Time elapsed: 0.047 s
% 0.22/0.51  % (29823)------------------------------
% 0.22/0.51  % (29823)------------------------------
% 0.22/0.51  % (29827)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (29816)Success in time 0.151 s
%------------------------------------------------------------------------------
