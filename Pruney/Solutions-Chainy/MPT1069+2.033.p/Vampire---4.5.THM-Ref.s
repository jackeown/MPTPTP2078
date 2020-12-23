%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 383 expanded)
%              Number of leaves         :   51 ( 179 expanded)
%              Depth                    :    9
%              Number of atoms          :  703 (1944 expanded)
%              Number of equality atoms :  141 ( 426 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f217,f481,f482,f489,f502,f528,f678,f689,f757,f884,f889,f892,f900,f938,f964,f968,f1046,f1176])).

fof(f1176,plain,
    ( ~ spl7_64
    | spl7_104
    | ~ spl7_65
    | ~ spl7_4
    | ~ spl7_91 ),
    inference(avatar_split_clause,[],[f1173,f898,f122,f695,f1029,f687])).

fof(f687,plain,
    ( spl7_64
  <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f1029,plain,
    ( spl7_104
  <=> ! [X5] :
        ( k1_xboole_0 = X5
        | ~ m1_subset_1(X5,k1_zfmisc_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f695,plain,
    ( spl7_65
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f122,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f898,plain,
    ( spl7_91
  <=> ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f1173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4)) )
    | ~ spl7_4
    | ~ spl7_91 ),
    inference(resolution,[],[f1120,f123])).

fof(f123,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1120,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_funct_2(sK3,X0,k1_relat_1(sK4)) )
    | ~ spl7_91 ),
    inference(resolution,[],[f899,f178])).

fof(f178,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,X2) ) ),
    inference(resolution,[],[f176,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f91,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f899,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) )
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f898])).

fof(f1046,plain,
    ( spl7_2
    | ~ spl7_53
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f1045,f1029,f526,f114])).

fof(f114,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f526,plain,
    ( spl7_53
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f1045,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_53
    | ~ spl7_104 ),
    inference(resolution,[],[f1039,f527])).

fof(f527,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f526])).

fof(f1039,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0 )
    | ~ spl7_104 ),
    inference(resolution,[],[f1030,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1030,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK1))
        | k1_xboole_0 = X5 )
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f1029])).

fof(f968,plain,
    ( spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_2
    | ~ spl7_78
    | spl7_1 ),
    inference(avatar_split_clause,[],[f799,f110,f806,f114,f118,f122,f126,f130,f134,f138,f142,f146])).

fof(f146,plain,
    ( spl7_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f142,plain,
    ( spl7_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f138,plain,
    ( spl7_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f134,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f130,plain,
    ( spl7_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f126,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f118,plain,
    ( spl7_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f806,plain,
    ( spl7_78
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f110,plain,
    ( spl7_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f799,plain,
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
    inference(superposition,[],[f111,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f111,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f964,plain,
    ( ~ spl7_50
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f519,f500,f504])).

fof(f504,plain,
    ( spl7_50
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f500,plain,
    ( spl7_49
  <=> ! [X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK6(sK1),X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f519,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_49 ),
    inference(superposition,[],[f501,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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

fof(f501,plain,
    ( ! [X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK6(sK1),X1)))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f500])).

% (2929)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f938,plain,
    ( spl7_50
    | ~ spl7_57
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f936,f695,f628,f504])).

fof(f628,plain,
    ( spl7_57
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f936,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_57
    | ~ spl7_65 ),
    inference(forward_demodulation,[],[f923,f99])).

fof(f923,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl7_57
    | ~ spl7_65 ),
    inference(superposition,[],[f756,f693])).

fof(f693,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f628])).

fof(f756,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f695])).

fof(f900,plain,
    ( spl7_57
    | spl7_91
    | ~ spl7_9
    | spl7_90 ),
    inference(avatar_split_clause,[],[f895,f882,f142,f898,f628])).

fof(f882,plain,
    ( spl7_90
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f895,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))
        | ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | k1_xboole_0 = k1_relat_1(sK4) )
    | ~ spl7_9
    | spl7_90 ),
    inference(resolution,[],[f883,f621])).

fof(f621,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(k1_funct_1(sK3,X4),X3)
        | ~ r2_hidden(X4,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X3)))
        | ~ v1_funct_2(sK3,X5,X3)
        | k1_xboole_0 = X3 )
    | ~ spl7_9 ),
    inference(resolution,[],[f92,f143])).

fof(f143,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f883,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl7_90 ),
    inference(avatar_component_clause,[],[f882])).

fof(f892,plain,
    ( ~ spl7_5
    | spl7_89 ),
    inference(avatar_contradiction_clause,[],[f891])).

fof(f891,plain,
    ( $false
    | ~ spl7_5
    | spl7_89 ),
    inference(subsumption_resolution,[],[f127,f890])).

fof(f890,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl7_89 ),
    inference(resolution,[],[f880,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f880,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | spl7_89 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl7_89
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f127,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f889,plain,
    ( ~ spl7_5
    | spl7_88 ),
    inference(avatar_contradiction_clause,[],[f886])).

fof(f886,plain,
    ( $false
    | ~ spl7_5
    | spl7_88 ),
    inference(subsumption_resolution,[],[f127,f885])).

fof(f885,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_88 ),
    inference(resolution,[],[f877,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f877,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_88 ),
    inference(avatar_component_clause,[],[f876])).

fof(f876,plain,
    ( spl7_88
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f884,plain,
    ( ~ spl7_88
    | ~ spl7_89
    | ~ spl7_6
    | ~ spl7_90
    | spl7_78 ),
    inference(avatar_split_clause,[],[f874,f806,f882,f130,f879,f876])).

fof(f874,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl7_78 ),
    inference(trivial_inequality_removal,[],[f873])).

fof(f873,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl7_78 ),
    inference(superposition,[],[f807,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f807,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl7_78 ),
    inference(avatar_component_clause,[],[f806])).

fof(f757,plain,
    ( spl7_65
    | ~ spl7_8
    | ~ spl7_7
    | spl7_45
    | ~ spl7_9
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f751,f215,f142,f476,f134,f138,f695])).

fof(f476,plain,
    ( spl7_45
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f215,plain,
    ( spl7_16
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f751,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | ~ spl7_9
    | ~ spl7_16 ),
    inference(resolution,[],[f744,f216])).

fof(f216,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f215])).

fof(f744,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(k2_relset_1(X4,X3,sK3),X5)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
        | ~ v1_funct_2(sK3,X4,X3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl7_9 ),
    inference(resolution,[],[f97,f143])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f689,plain,
    ( spl7_64
    | ~ spl7_16
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f680,f676,f215,f687])).

fof(f676,plain,
    ( spl7_62
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | v1_funct_2(sK3,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f680,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ spl7_16
    | ~ spl7_62 ),
    inference(resolution,[],[f677,f216])).

fof(f677,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | v1_funct_2(sK3,sK1,X0) )
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f676])).

fof(f678,plain,
    ( spl7_45
    | ~ spl7_7
    | spl7_62
    | ~ spl7_8
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f666,f142,f138,f676,f134,f476])).

fof(f666,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | k1_xboole_0 = sK2
        | v1_funct_2(sK3,sK1,X0) )
    | ~ spl7_8
    | ~ spl7_9 ),
    inference(resolution,[],[f662,f139])).

fof(f139,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f662,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_2(sK3,X4,X3)
        | ~ r1_tarski(k2_relset_1(X4,X3,sK3),X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
        | k1_xboole_0 = X3
        | v1_funct_2(sK3,X4,X5) )
    | ~ spl7_9 ),
    inference(resolution,[],[f95,f143])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f528,plain,
    ( spl7_53
    | ~ spl7_7
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f521,f486,f134,f526])).

fof(f486,plain,
    ( spl7_47
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f521,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl7_7
    | ~ spl7_47 ),
    inference(resolution,[],[f493,f135])).

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f493,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | r1_tarski(sK1,X2) )
    | ~ spl7_47 ),
    inference(superposition,[],[f227,f487])).

fof(f487,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f486])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(global_subsumption,[],[f69,f80,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f502,plain,
    ( spl7_2
    | spl7_49
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f491,f486,f500,f114])).

fof(f491,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK6(sK1),X1)))
        | k1_xboole_0 = sK1 )
    | ~ spl7_47 ),
    inference(superposition,[],[f234,f487])).

fof(f234,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(sK6(k1_relat_1(X12)),X13)))
      | k1_xboole_0 = k1_relat_1(X12) ) ),
    inference(resolution,[],[f227,f169])).

fof(f169,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK6(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f68,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f489,plain,
    ( ~ spl7_7
    | spl7_47
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f484,f479,f486,f134])).

fof(f479,plain,
    ( spl7_46
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f484,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_46 ),
    inference(superposition,[],[f81,f480])).

fof(f480,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f479])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f482,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f481,plain,
    ( ~ spl7_7
    | spl7_45
    | spl7_46
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f471,f138,f479,f476,f134])).

fof(f471,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_8 ),
    inference(resolution,[],[f84,f139])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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

fof(f217,plain,
    ( ~ spl7_5
    | spl7_16
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f212,f118,f215,f126])).

fof(f212,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl7_3 ),
    inference(superposition,[],[f119,f81])).

fof(f119,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f152,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f66,f150])).

fof(f150,plain,
    ( spl7_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f148,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f56,f146])).

fof(f56,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f47,f46,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f144,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f57,f142])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f140,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f58,f138])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f136,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f59,f134])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f132,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f60,f130])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f128,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f61,f126])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f124,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f62,f122])).

fof(f62,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f120,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f63,f118])).

fof(f63,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f116,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f64,f114])).

fof(f64,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f112,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f65,f110])).

fof(f65,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (2919)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (2919)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f1177,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f217,f481,f482,f489,f502,f528,f678,f689,f757,f884,f889,f892,f900,f938,f964,f968,f1046,f1176])).
% 0.21/0.46  fof(f1176,plain,(
% 0.21/0.46    ~spl7_64 | spl7_104 | ~spl7_65 | ~spl7_4 | ~spl7_91),
% 0.21/0.46    inference(avatar_split_clause,[],[f1173,f898,f122,f695,f1029,f687])).
% 0.21/0.46  fof(f687,plain,(
% 0.21/0.46    spl7_64 <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 0.21/0.46  fof(f1029,plain,(
% 0.21/0.46    spl7_104 <=> ! [X5] : (k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).
% 0.21/0.46  fof(f695,plain,(
% 0.21/0.46    spl7_65 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    spl7_4 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.46  fof(f898,plain,(
% 0.21/0.46    spl7_91 <=> ! [X0] : (~r2_hidden(sK5,X0) | ~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).
% 0.21/0.46  fof(f1173,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v1_funct_2(sK3,sK1,k1_relat_1(sK4))) ) | (~spl7_4 | ~spl7_91)),
% 0.21/0.46    inference(resolution,[],[f1120,f123])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    m1_subset_1(sK5,sK1) | ~spl7_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f122])).
% 0.21/0.46  fof(f1120,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK5,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_2(sK3,X0,k1_relat_1(sK4))) ) | ~spl7_91),
% 0.21/0.46    inference(resolution,[],[f899,f178])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,X2)) )),
% 0.21/0.46    inference(resolution,[],[f176,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(resolution,[],[f91,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.46  fof(f899,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK5,X0) | ~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))) ) | ~spl7_91),
% 0.21/0.46    inference(avatar_component_clause,[],[f898])).
% 0.21/0.46  fof(f1046,plain,(
% 0.21/0.46    spl7_2 | ~spl7_53 | ~spl7_104),
% 0.21/0.46    inference(avatar_split_clause,[],[f1045,f1029,f526,f114])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.46  fof(f526,plain,(
% 0.21/0.46    spl7_53 <=> r1_tarski(sK1,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 0.21/0.46  fof(f1045,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | (~spl7_53 | ~spl7_104)),
% 0.21/0.46    inference(resolution,[],[f1039,f527])).
% 0.21/0.46  fof(f527,plain,(
% 0.21/0.46    r1_tarski(sK1,sK1) | ~spl7_53),
% 0.21/0.46    inference(avatar_component_clause,[],[f526])).
% 0.21/0.46  fof(f1039,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0) ) | ~spl7_104),
% 0.21/0.46    inference(resolution,[],[f1030,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f1030,plain,(
% 0.21/0.46    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(sK1)) | k1_xboole_0 = X5) ) | ~spl7_104),
% 0.21/0.46    inference(avatar_component_clause,[],[f1029])).
% 0.21/0.46  fof(f968,plain,(
% 0.21/0.46    spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_7 | ~spl7_6 | ~spl7_5 | ~spl7_4 | ~spl7_3 | spl7_2 | ~spl7_78 | spl7_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f799,f110,f806,f114,f118,f122,f126,f130,f134,f138,f142,f146])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    spl7_10 <=> v1_xboole_0(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    spl7_9 <=> v1_funct_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    spl7_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    spl7_6 <=> v1_funct_1(sK4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    spl7_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    spl7_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.46  fof(f806,plain,(
% 0.21/0.46    spl7_78 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl7_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.46  fof(f799,plain,(
% 0.21/0.46    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2) | spl7_1),
% 0.21/0.46    inference(superposition,[],[f111,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.46    inference(flattening,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl7_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f110])).
% 0.21/0.46  fof(f964,plain,(
% 0.21/0.46    ~spl7_50 | ~spl7_49),
% 0.21/0.46    inference(avatar_split_clause,[],[f519,f500,f504])).
% 0.21/0.46  fof(f504,plain,(
% 0.21/0.46    spl7_50 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 0.21/0.46  fof(f500,plain,(
% 0.21/0.46    spl7_49 <=> ! [X1] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK6(sK1),X1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 0.21/0.46  fof(f519,plain,(
% 0.21/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_49),
% 0.21/0.46    inference(superposition,[],[f501,f99])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.46    inference(flattening,[],[f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.46  fof(f501,plain,(
% 0.21/0.46    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK6(sK1),X1)))) ) | ~spl7_49),
% 0.21/0.46    inference(avatar_component_clause,[],[f500])).
% 0.21/0.46  % (2929)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  fof(f938,plain,(
% 0.21/0.46    spl7_50 | ~spl7_57 | ~spl7_65),
% 0.21/0.46    inference(avatar_split_clause,[],[f936,f695,f628,f504])).
% 0.21/0.46  fof(f628,plain,(
% 0.21/0.46    spl7_57 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 0.21/0.46  fof(f936,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl7_57 | ~spl7_65)),
% 0.21/0.46    inference(forward_demodulation,[],[f923,f99])).
% 0.21/0.46  fof(f923,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl7_57 | ~spl7_65)),
% 0.21/0.46    inference(superposition,[],[f756,f693])).
% 0.21/0.46  fof(f693,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(sK4) | ~spl7_57),
% 0.21/0.46    inference(avatar_component_clause,[],[f628])).
% 0.21/0.46  fof(f756,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | ~spl7_65),
% 0.21/0.46    inference(avatar_component_clause,[],[f695])).
% 0.21/0.46  fof(f900,plain,(
% 0.21/0.46    spl7_57 | spl7_91 | ~spl7_9 | spl7_90),
% 0.21/0.46    inference(avatar_split_clause,[],[f895,f882,f142,f898,f628])).
% 0.21/0.46  fof(f882,plain,(
% 0.21/0.46    spl7_90 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).
% 0.21/0.46  fof(f895,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK5,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) | ~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | k1_xboole_0 = k1_relat_1(sK4)) ) | (~spl7_9 | spl7_90)),
% 0.21/0.46    inference(resolution,[],[f883,f621])).
% 0.21/0.46  fof(f621,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (r2_hidden(k1_funct_1(sK3,X4),X3) | ~r2_hidden(X4,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X3))) | ~v1_funct_2(sK3,X5,X3) | k1_xboole_0 = X3) ) | ~spl7_9),
% 0.21/0.46    inference(resolution,[],[f92,f143])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    v1_funct_1(sK3) | ~spl7_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f142])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.46    inference(flattening,[],[f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.46    inference(ennf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.46  fof(f883,plain,(
% 0.21/0.46    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl7_90),
% 0.21/0.46    inference(avatar_component_clause,[],[f882])).
% 0.21/0.46  fof(f892,plain,(
% 0.21/0.46    ~spl7_5 | spl7_89),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f891])).
% 0.21/0.46  fof(f891,plain,(
% 0.21/0.46    $false | (~spl7_5 | spl7_89)),
% 0.21/0.46    inference(subsumption_resolution,[],[f127,f890])).
% 0.21/0.46  fof(f890,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl7_89),
% 0.21/0.46    inference(resolution,[],[f880,f83])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.46  fof(f880,plain,(
% 0.21/0.46    ~v5_relat_1(sK4,sK0) | spl7_89),
% 0.21/0.46    inference(avatar_component_clause,[],[f879])).
% 0.21/0.46  fof(f879,plain,(
% 0.21/0.46    spl7_89 <=> v5_relat_1(sK4,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl7_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f126])).
% 0.21/0.46  fof(f889,plain,(
% 0.21/0.46    ~spl7_5 | spl7_88),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f886])).
% 0.21/0.46  fof(f886,plain,(
% 0.21/0.46    $false | (~spl7_5 | spl7_88)),
% 0.21/0.46    inference(subsumption_resolution,[],[f127,f885])).
% 0.21/0.46  fof(f885,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_88),
% 0.21/0.46    inference(resolution,[],[f877,f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  fof(f877,plain,(
% 0.21/0.46    ~v1_relat_1(sK4) | spl7_88),
% 0.21/0.46    inference(avatar_component_clause,[],[f876])).
% 0.21/0.46  fof(f876,plain,(
% 0.21/0.46    spl7_88 <=> v1_relat_1(sK4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).
% 0.21/0.46  fof(f884,plain,(
% 0.21/0.46    ~spl7_88 | ~spl7_89 | ~spl7_6 | ~spl7_90 | spl7_78),
% 0.21/0.46    inference(avatar_split_clause,[],[f874,f806,f882,f130,f879,f876])).
% 0.21/0.46  fof(f874,plain,(
% 0.21/0.46    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl7_78),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f873])).
% 0.21/0.46  fof(f873,plain,(
% 0.21/0.46    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl7_78),
% 0.21/0.46    inference(superposition,[],[f807,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.46  fof(f807,plain,(
% 0.21/0.46    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl7_78),
% 0.21/0.46    inference(avatar_component_clause,[],[f806])).
% 0.21/0.46  fof(f757,plain,(
% 0.21/0.46    spl7_65 | ~spl7_8 | ~spl7_7 | spl7_45 | ~spl7_9 | ~spl7_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f751,f215,f142,f476,f134,f138,f695])).
% 0.21/0.46  fof(f476,plain,(
% 0.21/0.46    spl7_45 <=> k1_xboole_0 = sK2),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    spl7_16 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.46  fof(f751,plain,(
% 0.21/0.46    k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | (~spl7_9 | ~spl7_16)),
% 0.21/0.46    inference(resolution,[],[f744,f216])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl7_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f215])).
% 0.21/0.46  fof(f744,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~r1_tarski(k2_relset_1(X4,X3,sK3),X5) | k1_xboole_0 = X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~v1_funct_2(sK3,X4,X3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | ~spl7_9),
% 0.21/0.46    inference(resolution,[],[f97,f143])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.46    inference(flattening,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.46    inference(ennf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.46  fof(f689,plain,(
% 0.21/0.46    spl7_64 | ~spl7_16 | ~spl7_62),
% 0.21/0.46    inference(avatar_split_clause,[],[f680,f676,f215,f687])).
% 0.21/0.46  fof(f676,plain,(
% 0.21/0.46    spl7_62 <=> ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | v1_funct_2(sK3,sK1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 0.21/0.46  fof(f680,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | (~spl7_16 | ~spl7_62)),
% 0.21/0.46    inference(resolution,[],[f677,f216])).
% 0.21/0.46  fof(f677,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | v1_funct_2(sK3,sK1,X0)) ) | ~spl7_62),
% 0.21/0.46    inference(avatar_component_clause,[],[f676])).
% 0.21/0.46  fof(f678,plain,(
% 0.21/0.46    spl7_45 | ~spl7_7 | spl7_62 | ~spl7_8 | ~spl7_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f666,f142,f138,f676,f134,f476])).
% 0.21/0.46  fof(f666,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X0)) ) | (~spl7_8 | ~spl7_9)),
% 0.21/0.46    inference(resolution,[],[f662,f139])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK1,sK2) | ~spl7_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f138])).
% 0.21/0.46  fof(f662,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~v1_funct_2(sK3,X4,X3) | ~r1_tarski(k2_relset_1(X4,X3,sK3),X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | k1_xboole_0 = X3 | v1_funct_2(sK3,X4,X5)) ) | ~spl7_9),
% 0.21/0.46    inference(resolution,[],[f95,f143])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | v1_funct_2(X3,X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f43])).
% 0.21/0.46  fof(f528,plain,(
% 0.21/0.46    spl7_53 | ~spl7_7 | ~spl7_47),
% 0.21/0.46    inference(avatar_split_clause,[],[f521,f486,f134,f526])).
% 0.21/0.46  fof(f486,plain,(
% 0.21/0.46    spl7_47 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.21/0.46  fof(f521,plain,(
% 0.21/0.46    r1_tarski(sK1,sK1) | (~spl7_7 | ~spl7_47)),
% 0.21/0.46    inference(resolution,[],[f493,f135])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f134])).
% 0.21/0.46  fof(f493,plain,(
% 0.21/0.46    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_tarski(sK1,X2)) ) | ~spl7_47),
% 0.21/0.46    inference(superposition,[],[f227,f487])).
% 0.21/0.46  fof(f487,plain,(
% 0.21/0.46    sK1 = k1_relat_1(sK3) | ~spl7_47),
% 0.21/0.46    inference(avatar_component_clause,[],[f486])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.46    inference(global_subsumption,[],[f69,f80,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f34])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.46  fof(f502,plain,(
% 0.21/0.46    spl7_2 | spl7_49 | ~spl7_47),
% 0.21/0.46    inference(avatar_split_clause,[],[f491,f486,f500,f114])).
% 0.21/0.46  fof(f491,plain,(
% 0.21/0.46    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK6(sK1),X1))) | k1_xboole_0 = sK1) ) | ~spl7_47),
% 0.21/0.46    inference(superposition,[],[f234,f487])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(sK6(k1_relat_1(X12)),X13))) | k1_xboole_0 = k1_relat_1(X12)) )),
% 0.21/0.46    inference(resolution,[],[f227,f169])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,sK6(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(resolution,[],[f68,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.46  fof(f489,plain,(
% 0.21/0.46    ~spl7_7 | spl7_47 | ~spl7_46),
% 0.21/0.46    inference(avatar_split_clause,[],[f484,f479,f486,f134])).
% 0.21/0.46  fof(f479,plain,(
% 0.21/0.46    spl7_46 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.21/0.46  fof(f484,plain,(
% 0.21/0.46    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_46),
% 0.21/0.46    inference(superposition,[],[f81,f480])).
% 0.21/0.46  fof(f480,plain,(
% 0.21/0.46    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl7_46),
% 0.21/0.46    inference(avatar_component_clause,[],[f479])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f482,plain,(
% 0.21/0.46    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f481,plain,(
% 0.21/0.46    ~spl7_7 | spl7_45 | spl7_46 | ~spl7_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f471,f138,f479,f476,f134])).
% 0.21/0.46  fof(f471,plain,(
% 0.21/0.46    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_8),
% 0.21/0.46    inference(resolution,[],[f84,f139])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(flattening,[],[f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    ~spl7_5 | spl7_16 | ~spl7_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f212,f118,f215,f126])).
% 0.21/0.46  fof(f212,plain,(
% 0.21/0.46    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl7_3),
% 0.21/0.46    inference(superposition,[],[f119,f81])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl7_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f118])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    spl7_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f66,f150])).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    spl7_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ~spl7_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f56,f146])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~v1_xboole_0(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f47,f46,f45,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f19])).
% 0.21/0.47  fof(f19,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    spl7_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f57,f142])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    v1_funct_1(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    spl7_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f58,f138])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl7_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f134])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl7_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f130])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    v1_funct_1(sK4)),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl7_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f126])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl7_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f122])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    m1_subset_1(sK5,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    spl7_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f63,f118])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ~spl7_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f64,f114])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ~spl7_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f110])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (2919)------------------------------
% 0.21/0.47  % (2919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2919)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (2919)Memory used [KB]: 11513
% 0.21/0.47  % (2919)Time elapsed: 0.045 s
% 0.21/0.47  % (2919)------------------------------
% 0.21/0.47  % (2919)------------------------------
% 0.21/0.47  % (2908)Success in time 0.117 s
%------------------------------------------------------------------------------
