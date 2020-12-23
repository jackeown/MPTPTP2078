%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:04 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  291 (1129 expanded)
%              Number of leaves         :   53 ( 356 expanded)
%              Depth                    :   19
%              Number of atoms          : 1003 (3849 expanded)
%              Number of equality atoms :  106 ( 524 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2356,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f153,f155,f168,f188,f200,f206,f310,f399,f408,f411,f460,f489,f509,f580,f610,f629,f644,f677,f719,f826,f1295,f1310,f1498,f1694,f1713,f1722,f1776,f2064,f2310,f2355])).

fof(f2355,plain,
    ( spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_62 ),
    inference(avatar_contradiction_clause,[],[f2351])).

fof(f2351,plain,
    ( $false
    | spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_62 ),
    inference(resolution,[],[f2345,f160])).

fof(f160,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f159,f80])).

fof(f80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f103,f89])).

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
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

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f66,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2345,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_62 ),
    inference(resolution,[],[f2342,f2160])).

fof(f2160,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f2159,f2094])).

fof(f2094,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f2093,f125])).

fof(f125,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2093,plain,
    ( k2_funct_1(k1_xboole_0) = k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f2092,f208])).

fof(f208,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_8 ),
    inference(resolution,[],[f205,f171])).

fof(f171,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f101,f160])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f205,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl6_8
  <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f2092,plain,
    ( k2_funct_1(k1_xboole_0) = k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl6_26
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f624,f1018])).

fof(f1018,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_26 ),
    inference(resolution,[],[f1015,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1015,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_26 ),
    inference(resolution,[],[f459,f90])).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f459,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK3)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl6_26
  <=> ! [X1] : ~ r2_hidden(X1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f624,plain,
    ( k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f622])).

fof(f622,plain,
    ( spl6_33
  <=> k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f2159,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1031,f2130])).

fof(f2130,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1783,f2098])).

fof(f2098,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33 ),
    inference(backward_demodulation,[],[f1347,f2094])).

fof(f1347,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f1053,f208])).

fof(f1053,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl6_26
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f609,f1018])).

fof(f609,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f607])).

fof(f607,plain,
    ( spl6_32
  <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f1783,plain,
    ( sK2 = k2_relat_1(k1_xboole_0)
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f309,f1344])).

fof(f1344,plain,
    ( ! [X0] : sK2 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f309,f1054])).

fof(f1054,plain,
    ( sK2 = k2_relat_1(k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f642,f1018])).

fof(f642,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f640])).

fof(f640,plain,
    ( spl6_36
  <=> sK2 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f309,plain,
    ( ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl6_11
  <=> ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f1031,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),sK2,sK1)
    | spl6_2
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f135,f1018])).

fof(f135,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_2
  <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f2342,plain,
    ( ! [X1] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
        | ~ r1_tarski(k1_xboole_0,X1) )
    | ~ spl6_62 ),
    inference(resolution,[],[f2309,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v1_funct_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ~ sP0(X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ~ sP0(X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2309,plain,
    ( ! [X0] :
        ( sP0(X0,k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f2308])).

fof(f2308,plain,
    ( spl6_62
  <=> ! [X0] :
        ( sP0(X0,k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f2310,plain,
    ( ~ spl6_9
    | ~ spl6_48
    | spl6_62
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f2303,f716,f640,f622,f607,f458,f308,f204,f2308,f1558,f262])).

fof(f262,plain,
    ( spl6_9
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1558,plain,
    ( spl6_48
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f716,plain,
    ( spl6_39
  <=> v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f2303,plain,
    ( ! [X0] :
        ( sP0(X0,k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_39 ),
    inference(resolution,[],[f2148,f141])).

fof(f141,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_2(X3,k1_xboole_0,X1)
      | sP0(X2,k1_xboole_0,X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X3) ) ),
    inference(forward_demodulation,[],[f127,f126])).

fof(f126,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f127,plain,(
    ! [X2,X3,X1] :
      ( sP0(X2,k1_xboole_0,X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X0,X3)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( sP0(X2,X0,X3)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_folding,[],[f53,f54])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f2148,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_36
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f1782,f2130])).

fof(f1782,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f1383,f208])).

fof(f1383,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK2)
    | ~ spl6_26
    | ~ spl6_39 ),
    inference(backward_demodulation,[],[f718,f1018])).

fof(f718,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f716])).

fof(f2064,plain,
    ( ~ spl6_8
    | ~ spl6_26
    | spl6_34
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f2058])).

fof(f2058,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_26
    | spl6_34
    | ~ spl6_36 ),
    inference(resolution,[],[f1903,f160])).

fof(f1903,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_26
    | spl6_34
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1902,f125])).

fof(f1902,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_26
    | spl6_34
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1862,f208])).

fof(f1862,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl6_26
    | spl6_34
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f1608,f1018])).

fof(f1608,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k1_xboole_0)
    | spl6_34
    | ~ spl6_36 ),
    inference(resolution,[],[f692,f216])).

fof(f216,plain,(
    ! [X2,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f214,f103])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f193,f80])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f102,f89])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f692,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3))
    | spl6_34
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f628,f642])).

fof(f628,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k2_funct_1(sK3))
    | spl6_34 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl6_34
  <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f1776,plain,
    ( ~ spl6_20
    | ~ spl6_1
    | ~ spl6_40
    | spl6_15
    | spl6_41
    | ~ spl6_1
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f1653,f640,f607,f577,f129,f815,f355,f811,f129,f401])).

fof(f401,plain,
    ( spl6_20
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f811,plain,
    ( spl6_40
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f355,plain,
    ( spl6_15
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f815,plain,
    ( spl6_41
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | sP0(X0,sK2,k2_funct_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f129,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f577,plain,
    ( spl6_29
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f1653,plain,
    ( ! [X4] :
        ( sP0(X4,sK2,k2_funct_1(sK3))
        | k1_xboole_0 = k1_relat_1(sK3)
        | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
        | ~ r1_tarski(k1_relat_1(sK3),X4)
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | ~ spl6_1
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1652,f682])).

fof(f682,plain,
    ( sK2 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_29
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f579,f642])).

fof(f579,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f577])).

fof(f1652,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k1_relat_1(sK3)
        | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
        | ~ r1_tarski(k1_relat_1(sK3),X4)
        | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3))
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | ~ spl6_1
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1651,f609])).

fof(f1651,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
        | ~ r1_tarski(k1_relat_1(sK3),X4)
        | k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))
        | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3))
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | ~ spl6_1
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1650,f682])).

fof(f1650,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))))
        | ~ r1_tarski(k1_relat_1(sK3),X4)
        | k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))
        | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3))
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | ~ spl6_1
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f1649,f609])).

fof(f1649,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(sK3),X4)
        | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
        | k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))
        | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3))
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | ~ spl6_1
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f1648,f609])).

fof(f1648,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X4)
        | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
        | k1_xboole_0 = k2_relat_1(k2_funct_1(sK3))
        | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3))
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f754,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f754,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_funct_2(k2_funct_1(sK3),X6,X4)
        | ~ r1_tarski(X4,X5)
        | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X6,X4)))
        | k1_xboole_0 = X4
        | sP0(X5,X6,k2_funct_1(sK3)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f121,f130])).

fof(f130,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | sP0(X2,X0,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1722,plain,
    ( spl6_3
    | ~ spl6_46
    | ~ spl6_49 ),
    inference(avatar_contradiction_clause,[],[f1717])).

fof(f1717,plain,
    ( $false
    | spl6_3
    | ~ spl6_46
    | ~ spl6_49 ),
    inference(resolution,[],[f1714,f139])).

fof(f139,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl6_3
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1714,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_46
    | ~ spl6_49 ),
    inference(resolution,[],[f1712,f1293])).

fof(f1293,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f1292,plain,
    ( spl6_46
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f1712,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f1711])).

fof(f1711,plain,
    ( spl6_49
  <=> ! [X0] :
        ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v4_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f1713,plain,
    ( ~ spl6_4
    | spl6_49
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f1706,f815,f1711,f146])).

fof(f146,plain,
    ( spl6_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1706,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_41 ),
    inference(resolution,[],[f1637,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1637,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) )
    | ~ spl6_41 ),
    inference(resolution,[],[f816,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f816,plain,
    ( ! [X0] :
        ( sP0(X0,sK2,k2_funct_1(sK3))
        | ~ r1_tarski(k1_relat_1(sK3),X0) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f815])).

fof(f1694,plain,(
    spl6_48 ),
    inference(avatar_contradiction_clause,[],[f1688])).

fof(f1688,plain,
    ( $false
    | spl6_48 ),
    inference(resolution,[],[f1684,f160])).

fof(f1684,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_48 ),
    inference(resolution,[],[f1559,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1559,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_48 ),
    inference(avatar_component_clause,[],[f1558])).

fof(f1498,plain,
    ( spl6_3
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f1492])).

fof(f1492,plain,
    ( $false
    | spl6_3
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(resolution,[],[f1332,f160])).

fof(f1332,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_3
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1331,f125])).

fof(f1331,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_xboole_0),k1_xboole_0)
    | spl6_3
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1067,f208])).

fof(f1067,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)),k1_xboole_0)
    | spl6_3
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f690,f1018])).

fof(f690,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k1_xboole_0)
    | spl6_3
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f618,f642])).

fof(f618,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k1_xboole_0)
    | spl6_3
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_32 ),
    inference(resolution,[],[f612,f278])).

fof(f278,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(X3))
        | ~ r1_tarski(X3,k1_xboole_0) )
    | spl6_3 ),
    inference(resolution,[],[f270,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_funct_1(sK3),X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | spl6_3 ),
    inference(resolution,[],[f238,f156])).

fof(f156,plain,
    ( ~ r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1))
    | spl6_3 ),
    inference(resolution,[],[f106,f139])).

fof(f238,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(X3,X4)
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f217,f103])).

fof(f217,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X4,X5)
      | ~ r1_tarski(X3,k1_xboole_0)
      | ~ r1_tarski(X5,X3) ) ),
    inference(resolution,[],[f214,f102])).

fof(f612,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f581,f609])).

fof(f581,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))))
    | ~ spl6_21
    | ~ spl6_29 ),
    inference(backward_demodulation,[],[f407,f579])).

fof(f407,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl6_21
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1310,plain,(
    spl6_46 ),
    inference(avatar_contradiction_clause,[],[f1307])).

fof(f1307,plain,
    ( $false
    | spl6_46 ),
    inference(resolution,[],[f1304,f76])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f56])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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

fof(f1304,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | spl6_46 ),
    inference(resolution,[],[f1294,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1294,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | spl6_46 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f1295,plain,
    ( ~ spl6_4
    | ~ spl6_46
    | spl6_2
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f1287,f815,f133,f1292,f146])).

fof(f1287,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | spl6_2
    | ~ spl6_41 ),
    inference(resolution,[],[f1286,f96])).

fof(f1286,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl6_2
    | ~ spl6_41 ),
    inference(resolution,[],[f1279,f135])).

fof(f1279,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_funct_1(sK3),sK2,X1)
        | ~ r1_tarski(k1_relat_1(sK3),X1) )
    | ~ spl6_41 ),
    inference(resolution,[],[f816,f119])).

fof(f826,plain,
    ( ~ spl6_21
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36
    | spl6_40 ),
    inference(resolution,[],[f813,f689])).

fof(f689,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f612,f642])).

fof(f813,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | spl6_40 ),
    inference(avatar_component_clause,[],[f811])).

fof(f719,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_39
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f714,f640,f716,f150,f146])).

fof(f150,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f714,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_36 ),
    inference(superposition,[],[f83,f642])).

fof(f677,plain,(
    spl6_35 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | spl6_35 ),
    inference(resolution,[],[f638,f76])).

fof(f638,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_35 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl6_35
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f644,plain,
    ( ~ spl6_35
    | spl6_36 ),
    inference(avatar_split_clause,[],[f634,f640,f636])).

fof(f634,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(superposition,[],[f78,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f78,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f629,plain,
    ( spl6_33
    | ~ spl6_34
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f620,f607,f577,f405,f626,f622])).

fof(f620,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_32 ),
    inference(resolution,[],[f612,f172])).

fof(f172,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | ~ r1_tarski(X4,X5)
      | X4 = X5 ) ),
    inference(resolution,[],[f101,f105])).

fof(f610,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_32 ),
    inference(avatar_split_clause,[],[f605,f607,f150,f146])).

fof(f605,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f77])).

fof(f77,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f580,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_29 ),
    inference(avatar_split_clause,[],[f575,f577,f150,f146])).

fof(f575,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f87,f77])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f509,plain,(
    spl6_25 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | spl6_25 ),
    inference(resolution,[],[f456,f160])).

fof(f456,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl6_25
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f489,plain,
    ( spl6_9
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl6_9
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(resolution,[],[f461,f264])).

fof(f264,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f262])).

fof(f461,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f74,f440])).

fof(f440,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(resolution,[],[f434,f178])).

fof(f178,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f171,f105])).

fof(f434,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f433,f126])).

fof(f433,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))))
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f398,f357])).

fof(f357,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f355])).

fof(f398,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl6_19
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f460,plain,
    ( ~ spl6_25
    | spl6_26
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f441,f396,f355,f458,f454])).

fof(f441,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | ~ r1_tarski(k1_xboole_0,k1_xboole_0) )
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(resolution,[],[f434,f235])).

fof(f235,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ r2_hidden(X4,X2)
      | ~ r1_tarski(X3,k1_xboole_0) ) ),
    inference(resolution,[],[f117,f215])).

fof(f215,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f214,f90])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f411,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_20 ),
    inference(avatar_split_clause,[],[f409,f401,f150,f146])).

fof(f409,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_20 ),
    inference(resolution,[],[f403,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f403,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f401])).

fof(f408,plain,
    ( ~ spl6_20
    | spl6_21
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f394,f129,f405,f401])).

fof(f394,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_1 ),
    inference(resolution,[],[f84,f130])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f399,plain,
    ( ~ spl6_4
    | spl6_19 ),
    inference(avatar_split_clause,[],[f392,f396,f146])).

fof(f392,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f84,f74])).

fof(f310,plain,
    ( ~ spl6_6
    | spl6_11
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f305,f186,f308,f182])).

fof(f182,plain,
    ( spl6_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f186,plain,
    ( spl6_7
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f305,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_7 ),
    inference(superposition,[],[f95,f187])).

fof(f187,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f206,plain,
    ( ~ spl6_6
    | spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f201,f186,f204,f182])).

fof(f201,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_7 ),
    inference(superposition,[],[f94,f187])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f200,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f195,f160])).

fof(f195,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_6 ),
    inference(resolution,[],[f191,f106])).

fof(f191,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_6 ),
    inference(superposition,[],[f189,f125])).

fof(f189,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_6 ),
    inference(resolution,[],[f184,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f184,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f182])).

fof(f188,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f176,f186,f182])).

fof(f176,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f171,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f168,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl6_4 ),
    inference(resolution,[],[f163,f76])).

fof(f163,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_4 ),
    inference(resolution,[],[f111,f148])).

fof(f148,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f155,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f152,f74])).

fof(f152,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f144,f129,f150,f146])).

fof(f144,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_1 ),
    inference(resolution,[],[f86,f131])).

fof(f131,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f140,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f79,f137,f133,f129])).

fof(f79,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (16243)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (16235)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (16236)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (16227)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (16228)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (16215)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (16216)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (16219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (16218)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (16220)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (16217)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (16225)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (16238)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (16244)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  % (16221)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (16230)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (16226)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (16224)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.59  % (16242)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.59  % (16240)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.59  % (16234)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.59  % (16239)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.59  % (16232)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.59  % (16233)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.60  % (16222)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.60  % (16237)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.61  % (16231)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.61  % (16223)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.61  % (16229)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.90/0.63  % (16241)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.19/0.66  % (16237)Refutation not found, incomplete strategy% (16237)------------------------------
% 2.19/0.66  % (16237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (16237)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (16237)Memory used [KB]: 11001
% 2.19/0.66  % (16237)Time elapsed: 0.236 s
% 2.19/0.66  % (16237)------------------------------
% 2.19/0.66  % (16237)------------------------------
% 2.19/0.70  % (16227)Refutation found. Thanks to Tanya!
% 2.19/0.70  % SZS status Theorem for theBenchmark
% 2.57/0.71  % SZS output start Proof for theBenchmark
% 2.57/0.71  fof(f2356,plain,(
% 2.57/0.71    $false),
% 2.57/0.71    inference(avatar_sat_refutation,[],[f140,f153,f155,f168,f188,f200,f206,f310,f399,f408,f411,f460,f489,f509,f580,f610,f629,f644,f677,f719,f826,f1295,f1310,f1498,f1694,f1713,f1722,f1776,f2064,f2310,f2355])).
% 2.57/0.71  fof(f2355,plain,(
% 2.57/0.71    spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36 | ~spl6_62),
% 2.57/0.71    inference(avatar_contradiction_clause,[],[f2351])).
% 2.57/0.71  fof(f2351,plain,(
% 2.57/0.71    $false | (spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36 | ~spl6_62)),
% 2.57/0.71    inference(resolution,[],[f2345,f160])).
% 2.57/0.71  fof(f160,plain,(
% 2.57/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.57/0.71    inference(resolution,[],[f159,f80])).
% 2.57/0.71  fof(f80,plain,(
% 2.57/0.71    v1_xboole_0(k1_xboole_0)),
% 2.57/0.71    inference(cnf_transformation,[],[f3])).
% 2.57/0.71  fof(f3,axiom,(
% 2.57/0.71    v1_xboole_0(k1_xboole_0)),
% 2.57/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.57/0.71  fof(f159,plain,(
% 2.57/0.71    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 2.57/0.71    inference(resolution,[],[f103,f89])).
% 2.57/0.71  fof(f89,plain,(
% 2.57/0.71    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.57/0.71    inference(cnf_transformation,[],[f61])).
% 2.57/0.71  fof(f61,plain,(
% 2.57/0.71    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.57/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).
% 2.57/0.71  fof(f60,plain,(
% 2.57/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.57/0.71    introduced(choice_axiom,[])).
% 2.57/0.71  fof(f59,plain,(
% 2.57/0.71    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.57/0.71    inference(rectify,[],[f58])).
% 2.57/0.71  fof(f58,plain,(
% 2.57/0.71    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.57/0.71    inference(nnf_transformation,[],[f1])).
% 2.57/0.71  fof(f1,axiom,(
% 2.57/0.71    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.57/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.57/0.71  fof(f103,plain,(
% 2.57/0.71    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.57/0.71    inference(cnf_transformation,[],[f68])).
% 2.57/0.71  fof(f68,plain,(
% 2.57/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.57/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f66,f67])).
% 2.57/0.71  fof(f67,plain,(
% 2.57/0.71    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.57/0.71    introduced(choice_axiom,[])).
% 2.57/0.71  fof(f66,plain,(
% 2.57/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.57/0.71    inference(rectify,[],[f65])).
% 2.57/0.71  fof(f65,plain,(
% 2.57/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.57/0.71    inference(nnf_transformation,[],[f44])).
% 2.57/0.71  fof(f44,plain,(
% 2.57/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.57/0.71    inference(ennf_transformation,[],[f2])).
% 2.57/0.71  fof(f2,axiom,(
% 2.57/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.57/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.57/0.71  fof(f2345,plain,(
% 2.57/0.71    ~r1_tarski(k1_xboole_0,sK1) | (spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36 | ~spl6_62)),
% 2.57/0.71    inference(resolution,[],[f2342,f2160])).
% 2.57/0.71  fof(f2160,plain,(
% 2.57/0.71    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36)),
% 2.57/0.71    inference(forward_demodulation,[],[f2159,f2094])).
% 2.57/0.71  fof(f2094,plain,(
% 2.57/0.71    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl6_8 | ~spl6_26 | ~spl6_33)),
% 2.57/0.71    inference(forward_demodulation,[],[f2093,f125])).
% 2.57/0.71  fof(f125,plain,(
% 2.57/0.71    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.57/0.71    inference(equality_resolution,[],[f109])).
% 2.57/0.71  fof(f109,plain,(
% 2.57/0.71    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.57/0.71    inference(cnf_transformation,[],[f71])).
% 2.57/0.71  fof(f71,plain,(
% 2.57/0.71    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.57/0.71    inference(flattening,[],[f70])).
% 2.57/0.71  fof(f70,plain,(
% 2.57/0.71    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.57/0.71    inference(nnf_transformation,[],[f7])).
% 2.57/0.71  fof(f7,axiom,(
% 2.57/0.71    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.57/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.57/0.71  fof(f2093,plain,(
% 2.57/0.71    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_26 | ~spl6_33)),
% 2.57/0.71    inference(forward_demodulation,[],[f2092,f208])).
% 2.57/0.71  fof(f208,plain,(
% 2.57/0.71    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_8),
% 2.57/0.71    inference(resolution,[],[f205,f171])).
% 2.57/0.71  fof(f171,plain,(
% 2.57/0.71    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 2.57/0.71    inference(resolution,[],[f101,f160])).
% 2.57/0.71  fof(f101,plain,(
% 2.57/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.57/0.71    inference(cnf_transformation,[],[f64])).
% 2.57/0.71  fof(f64,plain,(
% 2.57/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.57/0.71    inference(flattening,[],[f63])).
% 2.57/0.71  fof(f63,plain,(
% 2.57/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.57/0.71    inference(nnf_transformation,[],[f5])).
% 2.57/0.71  fof(f5,axiom,(
% 2.57/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.57/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.57/0.71  fof(f205,plain,(
% 2.57/0.71    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | ~spl6_8),
% 2.57/0.71    inference(avatar_component_clause,[],[f204])).
% 2.57/0.71  fof(f204,plain,(
% 2.57/0.71    spl6_8 <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)),
% 2.57/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.57/0.71  fof(f2092,plain,(
% 2.57/0.71    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) | (~spl6_26 | ~spl6_33)),
% 2.57/0.71    inference(forward_demodulation,[],[f624,f1018])).
% 2.57/0.71  fof(f1018,plain,(
% 2.57/0.71    k1_xboole_0 = sK3 | ~spl6_26),
% 2.57/0.71    inference(resolution,[],[f1015,f81])).
% 2.57/0.71  fof(f81,plain,(
% 2.57/0.71    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.57/0.71    inference(cnf_transformation,[],[f29])).
% 2.57/0.71  fof(f29,plain,(
% 2.57/0.71    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.57/0.71    inference(ennf_transformation,[],[f4])).
% 2.57/0.71  fof(f4,axiom,(
% 2.57/0.71    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.57/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.57/0.71  fof(f1015,plain,(
% 2.57/0.71    v1_xboole_0(sK3) | ~spl6_26),
% 2.57/0.71    inference(resolution,[],[f459,f90])).
% 2.57/0.71  fof(f90,plain,(
% 2.57/0.71    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 2.57/0.71    inference(cnf_transformation,[],[f61])).
% 2.57/0.71  fof(f459,plain,(
% 2.57/0.71    ( ! [X1] : (~r2_hidden(X1,sK3)) ) | ~spl6_26),
% 2.57/0.71    inference(avatar_component_clause,[],[f458])).
% 2.57/0.71  fof(f458,plain,(
% 2.57/0.71    spl6_26 <=> ! [X1] : ~r2_hidden(X1,sK3)),
% 2.57/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.57/0.71  fof(f624,plain,(
% 2.57/0.71    k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)) | ~spl6_33),
% 2.57/0.71    inference(avatar_component_clause,[],[f622])).
% 2.57/0.71  fof(f622,plain,(
% 2.57/0.71    spl6_33 <=> k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))),
% 2.57/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 2.57/0.71  fof(f2159,plain,(
% 2.57/0.71    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | (spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36)),
% 2.57/0.71    inference(forward_demodulation,[],[f1031,f2130])).
% 2.57/0.71  fof(f2130,plain,(
% 2.57/0.71    k1_xboole_0 = sK2 | (~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36)),
% 2.57/0.71    inference(forward_demodulation,[],[f1783,f2098])).
% 2.57/0.71  fof(f2098,plain,(
% 2.57/0.71    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl6_8 | ~spl6_26 | ~spl6_32 | ~spl6_33)),
% 2.57/0.71    inference(backward_demodulation,[],[f1347,f2094])).
% 2.57/0.71  fof(f1347,plain,(
% 2.57/0.71    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl6_8 | ~spl6_26 | ~spl6_32)),
% 2.57/0.71    inference(forward_demodulation,[],[f1053,f208])).
% 2.57/0.71  fof(f1053,plain,(
% 2.57/0.71    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl6_26 | ~spl6_32)),
% 2.57/0.71    inference(backward_demodulation,[],[f609,f1018])).
% 2.57/0.71  fof(f609,plain,(
% 2.57/0.71    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~spl6_32),
% 2.57/0.71    inference(avatar_component_clause,[],[f607])).
% 2.57/0.71  fof(f607,plain,(
% 2.57/0.71    spl6_32 <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 2.57/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 2.57/0.71  fof(f1783,plain,(
% 2.57/0.71    sK2 = k2_relat_1(k1_xboole_0) | (~spl6_11 | ~spl6_26 | ~spl6_36)),
% 2.57/0.71    inference(backward_demodulation,[],[f309,f1344])).
% 2.57/0.71  fof(f1344,plain,(
% 2.57/0.71    ( ! [X0] : (sK2 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl6_11 | ~spl6_26 | ~spl6_36)),
% 2.57/0.71    inference(backward_demodulation,[],[f309,f1054])).
% 2.57/0.71  fof(f1054,plain,(
% 2.57/0.71    sK2 = k2_relat_1(k1_xboole_0) | (~spl6_26 | ~spl6_36)),
% 2.57/0.71    inference(backward_demodulation,[],[f642,f1018])).
% 2.57/0.71  fof(f642,plain,(
% 2.57/0.71    sK2 = k2_relat_1(sK3) | ~spl6_36),
% 2.57/0.71    inference(avatar_component_clause,[],[f640])).
% 2.57/0.71  fof(f640,plain,(
% 2.57/0.71    spl6_36 <=> sK2 = k2_relat_1(sK3)),
% 2.57/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 2.57/0.71  fof(f309,plain,(
% 2.57/0.71    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | ~spl6_11),
% 2.57/0.71    inference(avatar_component_clause,[],[f308])).
% 2.57/0.72  fof(f308,plain,(
% 2.57/0.72    spl6_11 <=> ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.57/0.72  fof(f1031,plain,(
% 2.57/0.72    ~v1_funct_2(k2_funct_1(k1_xboole_0),sK2,sK1) | (spl6_2 | ~spl6_26)),
% 2.57/0.72    inference(backward_demodulation,[],[f135,f1018])).
% 2.57/0.72  fof(f135,plain,(
% 2.57/0.72    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | spl6_2),
% 2.57/0.72    inference(avatar_component_clause,[],[f133])).
% 2.57/0.72  fof(f133,plain,(
% 2.57/0.72    spl6_2 <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1)),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.57/0.72  fof(f2342,plain,(
% 2.57/0.72    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1) | ~r1_tarski(k1_xboole_0,X1)) ) | ~spl6_62),
% 2.57/0.72    inference(resolution,[],[f2309,f119])).
% 2.57/0.72  fof(f119,plain,(
% 2.57/0.72    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v1_funct_2(X2,X1,X0)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f73])).
% 2.57/0.72  fof(f73,plain,(
% 2.57/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP0(X0,X1,X2))),
% 2.57/0.72    inference(rectify,[],[f72])).
% 2.57/0.72  fof(f72,plain,(
% 2.57/0.72    ! [X2,X0,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | ~sP0(X2,X0,X3))),
% 2.57/0.72    inference(nnf_transformation,[],[f54])).
% 2.57/0.72  fof(f54,plain,(
% 2.57/0.72    ! [X2,X0,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | ~sP0(X2,X0,X3))),
% 2.57/0.72    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.57/0.72  fof(f2309,plain,(
% 2.57/0.72    ( ! [X0] : (sP0(X0,k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl6_62),
% 2.57/0.72    inference(avatar_component_clause,[],[f2308])).
% 2.57/0.72  fof(f2308,plain,(
% 2.57/0.72    spl6_62 <=> ! [X0] : (sP0(X0,k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 2.57/0.72  fof(f2310,plain,(
% 2.57/0.72    ~spl6_9 | ~spl6_48 | spl6_62 | ~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36 | ~spl6_39),
% 2.57/0.72    inference(avatar_split_clause,[],[f2303,f716,f640,f622,f607,f458,f308,f204,f2308,f1558,f262])).
% 2.57/0.72  fof(f262,plain,(
% 2.57/0.72    spl6_9 <=> v1_funct_1(k1_xboole_0)),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.57/0.72  fof(f1558,plain,(
% 2.57/0.72    spl6_48 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 2.57/0.72  fof(f716,plain,(
% 2.57/0.72    spl6_39 <=> v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 2.57/0.72  fof(f2303,plain,(
% 2.57/0.72    ( ! [X0] : (sP0(X0,k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0)) ) | (~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36 | ~spl6_39)),
% 2.57/0.72    inference(resolution,[],[f2148,f141])).
% 2.57/0.72  fof(f141,plain,(
% 2.57/0.72    ( ! [X2,X3,X1] : (~v1_funct_2(X3,k1_xboole_0,X1) | sP0(X2,k1_xboole_0,X3) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X3)) )),
% 2.57/0.72    inference(forward_demodulation,[],[f127,f126])).
% 2.57/0.72  fof(f126,plain,(
% 2.57/0.72    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.57/0.72    inference(equality_resolution,[],[f108])).
% 2.57/0.72  fof(f108,plain,(
% 2.57/0.72    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.57/0.72    inference(cnf_transformation,[],[f71])).
% 2.57/0.72  fof(f127,plain,(
% 2.57/0.72    ( ! [X2,X3,X1] : (sP0(X2,k1_xboole_0,X3) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 2.57/0.72    inference(equality_resolution,[],[f122])).
% 2.57/0.72  fof(f122,plain,(
% 2.57/0.72    ( ! [X2,X0,X3,X1] : (sP0(X2,X0,X3) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f55])).
% 2.57/0.72  fof(f55,plain,(
% 2.57/0.72    ! [X0,X1,X2,X3] : (sP0(X2,X0,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.57/0.72    inference(definition_folding,[],[f53,f54])).
% 2.57/0.72  fof(f53,plain,(
% 2.57/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.57/0.72    inference(flattening,[],[f52])).
% 2.57/0.72  fof(f52,plain,(
% 2.57/0.72    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.57/0.72    inference(ennf_transformation,[],[f24])).
% 2.57/0.72  fof(f24,axiom,(
% 2.57/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 2.57/0.72  fof(f2148,plain,(
% 2.57/0.72    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_32 | ~spl6_33 | ~spl6_36 | ~spl6_39)),
% 2.57/0.72    inference(forward_demodulation,[],[f1782,f2130])).
% 2.57/0.72  fof(f1782,plain,(
% 2.57/0.72    v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_8 | ~spl6_26 | ~spl6_39)),
% 2.57/0.72    inference(forward_demodulation,[],[f1383,f208])).
% 2.57/0.72  fof(f1383,plain,(
% 2.57/0.72    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK2) | (~spl6_26 | ~spl6_39)),
% 2.57/0.72    inference(backward_demodulation,[],[f718,f1018])).
% 2.57/0.72  fof(f718,plain,(
% 2.57/0.72    v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~spl6_39),
% 2.57/0.72    inference(avatar_component_clause,[],[f716])).
% 2.57/0.72  fof(f2064,plain,(
% 2.57/0.72    ~spl6_8 | ~spl6_26 | spl6_34 | ~spl6_36),
% 2.57/0.72    inference(avatar_contradiction_clause,[],[f2058])).
% 2.57/0.72  fof(f2058,plain,(
% 2.57/0.72    $false | (~spl6_8 | ~spl6_26 | spl6_34 | ~spl6_36)),
% 2.57/0.72    inference(resolution,[],[f1903,f160])).
% 2.57/0.72  fof(f1903,plain,(
% 2.57/0.72    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl6_8 | ~spl6_26 | spl6_34 | ~spl6_36)),
% 2.57/0.72    inference(forward_demodulation,[],[f1902,f125])).
% 2.57/0.72  fof(f1902,plain,(
% 2.57/0.72    ~r1_tarski(k2_zfmisc_1(sK2,k1_xboole_0),k1_xboole_0) | (~spl6_8 | ~spl6_26 | spl6_34 | ~spl6_36)),
% 2.57/0.72    inference(forward_demodulation,[],[f1862,f208])).
% 2.57/0.72  fof(f1862,plain,(
% 2.57/0.72    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)),k1_xboole_0) | (~spl6_26 | spl6_34 | ~spl6_36)),
% 2.57/0.72    inference(backward_demodulation,[],[f1608,f1018])).
% 2.57/0.72  fof(f1608,plain,(
% 2.57/0.72    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k1_xboole_0) | (spl6_34 | ~spl6_36)),
% 2.57/0.72    inference(resolution,[],[f692,f216])).
% 2.57/0.72  fof(f216,plain,(
% 2.57/0.72    ( ! [X2,X1] : (r1_tarski(X1,X2) | ~r1_tarski(X1,k1_xboole_0)) )),
% 2.57/0.72    inference(resolution,[],[f214,f103])).
% 2.57/0.72  fof(f214,plain,(
% 2.57/0.72    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.57/0.72    inference(resolution,[],[f193,f80])).
% 2.57/0.72  fof(f193,plain,(
% 2.57/0.72    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X1)) )),
% 2.57/0.72    inference(resolution,[],[f102,f89])).
% 2.57/0.72  fof(f102,plain,(
% 2.57/0.72    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f68])).
% 2.57/0.72  fof(f692,plain,(
% 2.57/0.72    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3)) | (spl6_34 | ~spl6_36)),
% 2.57/0.72    inference(backward_demodulation,[],[f628,f642])).
% 2.57/0.72  fof(f628,plain,(
% 2.57/0.72    ~r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k2_funct_1(sK3)) | spl6_34),
% 2.57/0.72    inference(avatar_component_clause,[],[f626])).
% 2.57/0.72  fof(f626,plain,(
% 2.57/0.72    spl6_34 <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k2_funct_1(sK3))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 2.57/0.72  fof(f1776,plain,(
% 2.57/0.72    ~spl6_20 | ~spl6_1 | ~spl6_40 | spl6_15 | spl6_41 | ~spl6_1 | ~spl6_29 | ~spl6_32 | ~spl6_36),
% 2.57/0.72    inference(avatar_split_clause,[],[f1653,f640,f607,f577,f129,f815,f355,f811,f129,f401])).
% 2.57/0.72  fof(f401,plain,(
% 2.57/0.72    spl6_20 <=> v1_relat_1(k2_funct_1(sK3))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.57/0.72  fof(f811,plain,(
% 2.57/0.72    spl6_40 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 2.57/0.72  fof(f355,plain,(
% 2.57/0.72    spl6_15 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.57/0.72  fof(f815,plain,(
% 2.57/0.72    spl6_41 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | sP0(X0,sK2,k2_funct_1(sK3)))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.57/0.72  fof(f129,plain,(
% 2.57/0.72    spl6_1 <=> v1_funct_1(k2_funct_1(sK3))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.57/0.72  fof(f577,plain,(
% 2.57/0.72    spl6_29 <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.57/0.72  fof(f1653,plain,(
% 2.57/0.72    ( ! [X4] : (sP0(X4,sK2,k2_funct_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | ~r1_tarski(k1_relat_1(sK3),X4) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) ) | (~spl6_1 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.72    inference(forward_demodulation,[],[f1652,f682])).
% 2.57/0.72  fof(f682,plain,(
% 2.57/0.72    sK2 = k1_relat_1(k2_funct_1(sK3)) | (~spl6_29 | ~spl6_36)),
% 2.57/0.72    inference(backward_demodulation,[],[f579,f642])).
% 2.57/0.72  fof(f579,plain,(
% 2.57/0.72    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~spl6_29),
% 2.57/0.72    inference(avatar_component_clause,[],[f577])).
% 2.57/0.72  fof(f1652,plain,(
% 2.57/0.72    ( ! [X4] : (k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | ~r1_tarski(k1_relat_1(sK3),X4) | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) ) | (~spl6_1 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.72    inference(forward_demodulation,[],[f1651,f609])).
% 2.57/0.72  fof(f1651,plain,(
% 2.57/0.72    ( ! [X4] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | ~r1_tarski(k1_relat_1(sK3),X4) | k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) ) | (~spl6_1 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.72    inference(forward_demodulation,[],[f1650,f682])).
% 2.57/0.72  fof(f1650,plain,(
% 2.57/0.72    ( ! [X4] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) | ~r1_tarski(k1_relat_1(sK3),X4) | k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) ) | (~spl6_1 | ~spl6_32)),
% 2.57/0.72    inference(forward_demodulation,[],[f1649,f609])).
% 2.57/0.72  fof(f1649,plain,(
% 2.57/0.72    ( ! [X4] : (~r1_tarski(k1_relat_1(sK3),X4) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) ) | (~spl6_1 | ~spl6_32)),
% 2.57/0.72    inference(forward_demodulation,[],[f1648,f609])).
% 2.57/0.72  fof(f1648,plain,(
% 2.57/0.72    ( ! [X4] : (~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X4) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | k1_xboole_0 = k2_relat_1(k2_funct_1(sK3)) | sP0(X4,k1_relat_1(k2_funct_1(sK3)),k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) ) | ~spl6_1),
% 2.57/0.72    inference(resolution,[],[f754,f83])).
% 2.57/0.72  fof(f83,plain,(
% 2.57/0.72    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f31])).
% 2.57/0.72  fof(f31,plain,(
% 2.57/0.72    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.57/0.72    inference(flattening,[],[f30])).
% 2.57/0.72  fof(f30,plain,(
% 2.57/0.72    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.57/0.72    inference(ennf_transformation,[],[f23])).
% 2.57/0.72  fof(f23,axiom,(
% 2.57/0.72    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 2.57/0.72  fof(f754,plain,(
% 2.57/0.72    ( ! [X6,X4,X5] : (~v1_funct_2(k2_funct_1(sK3),X6,X4) | ~r1_tarski(X4,X5) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X6,X4))) | k1_xboole_0 = X4 | sP0(X5,X6,k2_funct_1(sK3))) ) | ~spl6_1),
% 2.57/0.72    inference(resolution,[],[f121,f130])).
% 2.57/0.72  fof(f130,plain,(
% 2.57/0.72    v1_funct_1(k2_funct_1(sK3)) | ~spl6_1),
% 2.57/0.72    inference(avatar_component_clause,[],[f129])).
% 2.57/0.72  fof(f121,plain,(
% 2.57/0.72    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | sP0(X2,X0,X3)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f55])).
% 2.57/0.72  fof(f1722,plain,(
% 2.57/0.72    spl6_3 | ~spl6_46 | ~spl6_49),
% 2.57/0.72    inference(avatar_contradiction_clause,[],[f1717])).
% 2.57/0.72  fof(f1717,plain,(
% 2.57/0.72    $false | (spl6_3 | ~spl6_46 | ~spl6_49)),
% 2.57/0.72    inference(resolution,[],[f1714,f139])).
% 2.57/0.72  fof(f139,plain,(
% 2.57/0.72    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 2.57/0.72    inference(avatar_component_clause,[],[f137])).
% 2.57/0.72  fof(f137,plain,(
% 2.57/0.72    spl6_3 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.57/0.72  fof(f1714,plain,(
% 2.57/0.72    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl6_46 | ~spl6_49)),
% 2.57/0.72    inference(resolution,[],[f1712,f1293])).
% 2.57/0.72  fof(f1293,plain,(
% 2.57/0.72    v4_relat_1(sK3,sK1) | ~spl6_46),
% 2.57/0.72    inference(avatar_component_clause,[],[f1292])).
% 2.57/0.72  fof(f1292,plain,(
% 2.57/0.72    spl6_46 <=> v4_relat_1(sK3,sK1)),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 2.57/0.72  fof(f1712,plain,(
% 2.57/0.72    ( ! [X0] : (~v4_relat_1(sK3,X0) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | ~spl6_49),
% 2.57/0.72    inference(avatar_component_clause,[],[f1711])).
% 2.57/0.72  fof(f1711,plain,(
% 2.57/0.72    spl6_49 <=> ! [X0] : (m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v4_relat_1(sK3,X0))),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 2.57/0.72  fof(f1713,plain,(
% 2.57/0.72    ~spl6_4 | spl6_49 | ~spl6_41),
% 2.57/0.72    inference(avatar_split_clause,[],[f1706,f815,f1711,f146])).
% 2.57/0.72  fof(f146,plain,(
% 2.57/0.72    spl6_4 <=> v1_relat_1(sK3)),
% 2.57/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.57/0.72  fof(f1706,plain,(
% 2.57/0.72    ( ! [X0] : (m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | ~spl6_41),
% 2.57/0.72    inference(resolution,[],[f1637,f96])).
% 2.57/0.73  fof(f96,plain,(
% 2.57/0.73    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f62])).
% 2.57/0.73  fof(f62,plain,(
% 2.57/0.73    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.57/0.73    inference(nnf_transformation,[],[f41])).
% 2.57/0.73  fof(f41,plain,(
% 2.57/0.73    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.57/0.73    inference(ennf_transformation,[],[f10])).
% 2.57/0.73  fof(f10,axiom,(
% 2.57/0.73    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.57/0.73  fof(f1637,plain,(
% 2.57/0.73    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | ~spl6_41),
% 2.57/0.73    inference(resolution,[],[f816,f120])).
% 2.57/0.73  fof(f120,plain,(
% 2.57/0.73    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.57/0.73    inference(cnf_transformation,[],[f73])).
% 2.57/0.73  fof(f816,plain,(
% 2.57/0.73    ( ! [X0] : (sP0(X0,sK2,k2_funct_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),X0)) ) | ~spl6_41),
% 2.57/0.73    inference(avatar_component_clause,[],[f815])).
% 2.57/0.73  fof(f1694,plain,(
% 2.57/0.73    spl6_48),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f1688])).
% 2.57/0.73  fof(f1688,plain,(
% 2.57/0.73    $false | spl6_48),
% 2.57/0.73    inference(resolution,[],[f1684,f160])).
% 2.57/0.73  fof(f1684,plain,(
% 2.57/0.73    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl6_48),
% 2.57/0.73    inference(resolution,[],[f1559,f106])).
% 2.57/0.73  fof(f106,plain,(
% 2.57/0.73    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f69])).
% 2.57/0.73  fof(f69,plain,(
% 2.57/0.73    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.57/0.73    inference(nnf_transformation,[],[f8])).
% 2.57/0.73  fof(f8,axiom,(
% 2.57/0.73    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.57/0.73  fof(f1559,plain,(
% 2.57/0.73    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl6_48),
% 2.57/0.73    inference(avatar_component_clause,[],[f1558])).
% 2.57/0.73  fof(f1498,plain,(
% 2.57/0.73    spl6_3 | ~spl6_8 | ~spl6_21 | ~spl6_26 | ~spl6_29 | ~spl6_32 | ~spl6_36),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f1492])).
% 2.57/0.73  fof(f1492,plain,(
% 2.57/0.73    $false | (spl6_3 | ~spl6_8 | ~spl6_21 | ~spl6_26 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.73    inference(resolution,[],[f1332,f160])).
% 2.57/0.73  fof(f1332,plain,(
% 2.57/0.73    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl6_3 | ~spl6_8 | ~spl6_21 | ~spl6_26 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.73    inference(forward_demodulation,[],[f1331,f125])).
% 2.57/0.73  fof(f1331,plain,(
% 2.57/0.73    ~r1_tarski(k2_zfmisc_1(sK2,k1_xboole_0),k1_xboole_0) | (spl6_3 | ~spl6_8 | ~spl6_21 | ~spl6_26 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.73    inference(forward_demodulation,[],[f1067,f208])).
% 2.57/0.73  fof(f1067,plain,(
% 2.57/0.73    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)),k1_xboole_0) | (spl6_3 | ~spl6_21 | ~spl6_26 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.73    inference(backward_demodulation,[],[f690,f1018])).
% 2.57/0.73  fof(f690,plain,(
% 2.57/0.73    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k1_xboole_0) | (spl6_3 | ~spl6_21 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.73    inference(backward_demodulation,[],[f618,f642])).
% 2.57/0.73  fof(f618,plain,(
% 2.57/0.73    ~r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k1_xboole_0) | (spl6_3 | ~spl6_21 | ~spl6_29 | ~spl6_32)),
% 2.57/0.73    inference(resolution,[],[f612,f278])).
% 2.57/0.73  fof(f278,plain,(
% 2.57/0.73    ( ! [X3] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(X3)) | ~r1_tarski(X3,k1_xboole_0)) ) | spl6_3),
% 2.57/0.73    inference(resolution,[],[f270,f105])).
% 2.57/0.73  fof(f105,plain,(
% 2.57/0.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.57/0.73    inference(cnf_transformation,[],[f69])).
% 2.57/0.73  fof(f270,plain,(
% 2.57/0.73    ( ! [X0] : (~r1_tarski(k2_funct_1(sK3),X0) | ~r1_tarski(X0,k1_xboole_0)) ) | spl6_3),
% 2.57/0.73    inference(resolution,[],[f238,f156])).
% 2.57/0.73  fof(f156,plain,(
% 2.57/0.73    ~r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) | spl6_3),
% 2.57/0.73    inference(resolution,[],[f106,f139])).
% 2.57/0.73  fof(f238,plain,(
% 2.57/0.73    ( ! [X4,X2,X3] : (r1_tarski(X3,X4) | ~r1_tarski(X3,X2) | ~r1_tarski(X2,k1_xboole_0)) )),
% 2.57/0.73    inference(resolution,[],[f217,f103])).
% 2.57/0.73  fof(f217,plain,(
% 2.57/0.73    ( ! [X4,X5,X3] : (~r2_hidden(X4,X5) | ~r1_tarski(X3,k1_xboole_0) | ~r1_tarski(X5,X3)) )),
% 2.57/0.73    inference(resolution,[],[f214,f102])).
% 2.57/0.73  fof(f612,plain,(
% 2.57/0.73    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) | (~spl6_21 | ~spl6_29 | ~spl6_32)),
% 2.57/0.73    inference(backward_demodulation,[],[f581,f609])).
% 2.57/0.73  fof(f581,plain,(
% 2.57/0.73    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))) | (~spl6_21 | ~spl6_29)),
% 2.57/0.73    inference(backward_demodulation,[],[f407,f579])).
% 2.57/0.73  fof(f407,plain,(
% 2.57/0.73    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | ~spl6_21),
% 2.57/0.73    inference(avatar_component_clause,[],[f405])).
% 2.57/0.73  fof(f405,plain,(
% 2.57/0.73    spl6_21 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))),
% 2.57/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.57/0.73  fof(f1310,plain,(
% 2.57/0.73    spl6_46),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f1307])).
% 2.57/0.73  fof(f1307,plain,(
% 2.57/0.73    $false | spl6_46),
% 2.57/0.73    inference(resolution,[],[f1304,f76])).
% 2.57/0.73  fof(f76,plain,(
% 2.57/0.73    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.57/0.73    inference(cnf_transformation,[],[f57])).
% 2.57/0.73  fof(f57,plain,(
% 2.57/0.73    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.57/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f56])).
% 2.57/0.73  fof(f56,plain,(
% 2.57/0.73    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.57/0.73    introduced(choice_axiom,[])).
% 2.57/0.73  fof(f28,plain,(
% 2.57/0.73    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.57/0.73    inference(flattening,[],[f27])).
% 2.57/0.73  fof(f27,plain,(
% 2.57/0.73    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.57/0.73    inference(ennf_transformation,[],[f26])).
% 2.57/0.73  fof(f26,negated_conjecture,(
% 2.57/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.57/0.73    inference(negated_conjecture,[],[f25])).
% 2.57/0.73  fof(f25,conjecture,(
% 2.57/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 2.57/0.73  fof(f1304,plain,(
% 2.57/0.73    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl6_46),
% 2.57/0.73    inference(resolution,[],[f1294,f113])).
% 2.57/0.73  fof(f113,plain,(
% 2.57/0.73    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/0.73    inference(cnf_transformation,[],[f48])).
% 2.57/0.73  fof(f48,plain,(
% 2.57/0.73    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/0.73    inference(ennf_transformation,[],[f18])).
% 2.57/0.73  fof(f18,axiom,(
% 2.57/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.57/0.73  fof(f1294,plain,(
% 2.57/0.73    ~v4_relat_1(sK3,sK1) | spl6_46),
% 2.57/0.73    inference(avatar_component_clause,[],[f1292])).
% 2.57/0.73  fof(f1295,plain,(
% 2.57/0.73    ~spl6_4 | ~spl6_46 | spl6_2 | ~spl6_41),
% 2.57/0.73    inference(avatar_split_clause,[],[f1287,f815,f133,f1292,f146])).
% 2.57/0.73  fof(f1287,plain,(
% 2.57/0.73    ~v4_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | (spl6_2 | ~spl6_41)),
% 2.57/0.73    inference(resolution,[],[f1286,f96])).
% 2.57/0.73  fof(f1286,plain,(
% 2.57/0.73    ~r1_tarski(k1_relat_1(sK3),sK1) | (spl6_2 | ~spl6_41)),
% 2.57/0.73    inference(resolution,[],[f1279,f135])).
% 2.57/0.73  fof(f1279,plain,(
% 2.57/0.73    ( ! [X1] : (v1_funct_2(k2_funct_1(sK3),sK2,X1) | ~r1_tarski(k1_relat_1(sK3),X1)) ) | ~spl6_41),
% 2.57/0.73    inference(resolution,[],[f816,f119])).
% 2.57/0.73  fof(f826,plain,(
% 2.57/0.73    ~spl6_21 | ~spl6_29 | ~spl6_32 | ~spl6_36 | spl6_40),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f824])).
% 2.57/0.73  fof(f824,plain,(
% 2.57/0.73    $false | (~spl6_21 | ~spl6_29 | ~spl6_32 | ~spl6_36 | spl6_40)),
% 2.57/0.73    inference(resolution,[],[f813,f689])).
% 2.57/0.73  fof(f689,plain,(
% 2.57/0.73    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | (~spl6_21 | ~spl6_29 | ~spl6_32 | ~spl6_36)),
% 2.57/0.73    inference(backward_demodulation,[],[f612,f642])).
% 2.57/0.73  fof(f813,plain,(
% 2.57/0.73    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | spl6_40),
% 2.57/0.73    inference(avatar_component_clause,[],[f811])).
% 2.57/0.73  fof(f719,plain,(
% 2.57/0.73    ~spl6_4 | ~spl6_5 | spl6_39 | ~spl6_36),
% 2.57/0.73    inference(avatar_split_clause,[],[f714,f640,f716,f150,f146])).
% 2.57/0.73  fof(f150,plain,(
% 2.57/0.73    spl6_5 <=> v1_funct_1(sK3)),
% 2.57/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.57/0.73  fof(f714,plain,(
% 2.57/0.73    v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl6_36),
% 2.57/0.73    inference(superposition,[],[f83,f642])).
% 2.57/0.73  fof(f677,plain,(
% 2.57/0.73    spl6_35),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f675])).
% 2.57/0.73  fof(f675,plain,(
% 2.57/0.73    $false | spl6_35),
% 2.57/0.73    inference(resolution,[],[f638,f76])).
% 2.57/0.73  fof(f638,plain,(
% 2.57/0.73    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_35),
% 2.57/0.73    inference(avatar_component_clause,[],[f636])).
% 2.57/0.73  fof(f636,plain,(
% 2.57/0.73    spl6_35 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.57/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 2.57/0.73  fof(f644,plain,(
% 2.57/0.73    ~spl6_35 | spl6_36),
% 2.57/0.73    inference(avatar_split_clause,[],[f634,f640,f636])).
% 2.57/0.73  fof(f634,plain,(
% 2.57/0.73    sK2 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.57/0.73    inference(superposition,[],[f78,f112])).
% 2.57/0.73  fof(f112,plain,(
% 2.57/0.73    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/0.73    inference(cnf_transformation,[],[f47])).
% 2.57/0.73  fof(f47,plain,(
% 2.57/0.73    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/0.73    inference(ennf_transformation,[],[f20])).
% 2.57/0.73  fof(f20,axiom,(
% 2.57/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.57/0.73  fof(f78,plain,(
% 2.57/0.73    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 2.57/0.73    inference(cnf_transformation,[],[f57])).
% 2.57/0.73  fof(f629,plain,(
% 2.57/0.73    spl6_33 | ~spl6_34 | ~spl6_21 | ~spl6_29 | ~spl6_32),
% 2.57/0.73    inference(avatar_split_clause,[],[f620,f607,f577,f405,f626,f622])).
% 2.57/0.73  fof(f620,plain,(
% 2.57/0.73    ~r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)) | (~spl6_21 | ~spl6_29 | ~spl6_32)),
% 2.57/0.73    inference(resolution,[],[f612,f172])).
% 2.57/0.73  fof(f172,plain,(
% 2.57/0.73    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(X4)) | ~r1_tarski(X4,X5) | X4 = X5) )),
% 2.57/0.73    inference(resolution,[],[f101,f105])).
% 2.57/0.73  fof(f610,plain,(
% 2.57/0.73    ~spl6_4 | ~spl6_5 | spl6_32),
% 2.57/0.73    inference(avatar_split_clause,[],[f605,f607,f150,f146])).
% 2.57/0.73  fof(f605,plain,(
% 2.57/0.73    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.57/0.73    inference(resolution,[],[f88,f77])).
% 2.57/0.73  fof(f77,plain,(
% 2.57/0.73    v2_funct_1(sK3)),
% 2.57/0.73    inference(cnf_transformation,[],[f57])).
% 2.57/0.73  fof(f88,plain,(
% 2.57/0.73    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f35])).
% 2.57/0.73  fof(f35,plain,(
% 2.57/0.73    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.57/0.73    inference(flattening,[],[f34])).
% 2.57/0.73  fof(f34,plain,(
% 2.57/0.73    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.57/0.73    inference(ennf_transformation,[],[f16])).
% 2.57/0.73  fof(f16,axiom,(
% 2.57/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.57/0.73  fof(f580,plain,(
% 2.57/0.73    ~spl6_4 | ~spl6_5 | spl6_29),
% 2.57/0.73    inference(avatar_split_clause,[],[f575,f577,f150,f146])).
% 2.57/0.73  fof(f575,plain,(
% 2.57/0.73    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.57/0.73    inference(resolution,[],[f87,f77])).
% 2.57/0.73  fof(f87,plain,(
% 2.57/0.73    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f35])).
% 2.57/0.73  fof(f509,plain,(
% 2.57/0.73    spl6_25),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f503])).
% 2.57/0.73  fof(f503,plain,(
% 2.57/0.73    $false | spl6_25),
% 2.57/0.73    inference(resolution,[],[f456,f160])).
% 2.57/0.73  fof(f456,plain,(
% 2.57/0.73    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl6_25),
% 2.57/0.73    inference(avatar_component_clause,[],[f454])).
% 2.57/0.73  fof(f454,plain,(
% 2.57/0.73    spl6_25 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 2.57/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.57/0.73  fof(f489,plain,(
% 2.57/0.73    spl6_9 | ~spl6_15 | ~spl6_19),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f487])).
% 2.57/0.73  fof(f487,plain,(
% 2.57/0.73    $false | (spl6_9 | ~spl6_15 | ~spl6_19)),
% 2.57/0.73    inference(resolution,[],[f461,f264])).
% 2.57/0.73  fof(f264,plain,(
% 2.57/0.73    ~v1_funct_1(k1_xboole_0) | spl6_9),
% 2.57/0.73    inference(avatar_component_clause,[],[f262])).
% 2.57/0.73  fof(f461,plain,(
% 2.57/0.73    v1_funct_1(k1_xboole_0) | (~spl6_15 | ~spl6_19)),
% 2.57/0.73    inference(backward_demodulation,[],[f74,f440])).
% 2.57/0.73  fof(f440,plain,(
% 2.57/0.73    k1_xboole_0 = sK3 | (~spl6_15 | ~spl6_19)),
% 2.57/0.73    inference(resolution,[],[f434,f178])).
% 2.57/0.73  fof(f178,plain,(
% 2.57/0.73    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X1) )),
% 2.57/0.73    inference(resolution,[],[f171,f105])).
% 2.57/0.73  fof(f434,plain,(
% 2.57/0.73    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_15 | ~spl6_19)),
% 2.57/0.73    inference(forward_demodulation,[],[f433,f126])).
% 2.57/0.73  fof(f433,plain,(
% 2.57/0.73    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))) | (~spl6_15 | ~spl6_19)),
% 2.57/0.73    inference(backward_demodulation,[],[f398,f357])).
% 2.57/0.73  fof(f357,plain,(
% 2.57/0.73    k1_xboole_0 = k1_relat_1(sK3) | ~spl6_15),
% 2.57/0.73    inference(avatar_component_clause,[],[f355])).
% 2.57/0.73  fof(f398,plain,(
% 2.57/0.73    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl6_19),
% 2.57/0.73    inference(avatar_component_clause,[],[f396])).
% 2.57/0.73  fof(f396,plain,(
% 2.57/0.73    spl6_19 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 2.57/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.57/0.73  fof(f74,plain,(
% 2.57/0.73    v1_funct_1(sK3)),
% 2.57/0.73    inference(cnf_transformation,[],[f57])).
% 2.57/0.73  fof(f460,plain,(
% 2.57/0.73    ~spl6_25 | spl6_26 | ~spl6_15 | ~spl6_19),
% 2.57/0.73    inference(avatar_split_clause,[],[f441,f396,f355,f458,f454])).
% 2.57/0.73  fof(f441,plain,(
% 2.57/0.73    ( ! [X1] : (~r2_hidden(X1,sK3) | ~r1_tarski(k1_xboole_0,k1_xboole_0)) ) | (~spl6_15 | ~spl6_19)),
% 2.57/0.73    inference(resolution,[],[f434,f235])).
% 2.57/0.73  fof(f235,plain,(
% 2.57/0.73    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~r2_hidden(X4,X2) | ~r1_tarski(X3,k1_xboole_0)) )),
% 2.57/0.73    inference(resolution,[],[f117,f215])).
% 2.57/0.73  fof(f215,plain,(
% 2.57/0.73    ( ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.57/0.73    inference(resolution,[],[f214,f90])).
% 2.57/0.73  fof(f117,plain,(
% 2.57/0.73    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f51])).
% 2.57/0.73  fof(f51,plain,(
% 2.57/0.73    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.57/0.73    inference(ennf_transformation,[],[f9])).
% 2.57/0.73  fof(f9,axiom,(
% 2.57/0.73    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 2.57/0.73  fof(f411,plain,(
% 2.57/0.73    ~spl6_4 | ~spl6_5 | spl6_20),
% 2.57/0.73    inference(avatar_split_clause,[],[f409,f401,f150,f146])).
% 2.57/0.73  fof(f409,plain,(
% 2.57/0.73    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_20),
% 2.57/0.73    inference(resolution,[],[f403,f85])).
% 2.57/0.73  fof(f85,plain,(
% 2.57/0.73    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f33])).
% 2.57/0.73  fof(f33,plain,(
% 2.57/0.73    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.57/0.73    inference(flattening,[],[f32])).
% 2.57/0.73  fof(f32,plain,(
% 2.57/0.73    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.57/0.73    inference(ennf_transformation,[],[f14])).
% 2.57/0.73  fof(f14,axiom,(
% 2.57/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.57/0.73  fof(f403,plain,(
% 2.57/0.73    ~v1_relat_1(k2_funct_1(sK3)) | spl6_20),
% 2.57/0.73    inference(avatar_component_clause,[],[f401])).
% 2.57/0.73  fof(f408,plain,(
% 2.57/0.73    ~spl6_20 | spl6_21 | ~spl6_1),
% 2.57/0.73    inference(avatar_split_clause,[],[f394,f129,f405,f401])).
% 2.57/0.73  fof(f394,plain,(
% 2.57/0.73    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl6_1),
% 2.57/0.73    inference(resolution,[],[f84,f130])).
% 2.57/0.73  fof(f84,plain,(
% 2.57/0.73    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f31])).
% 2.57/0.73  fof(f399,plain,(
% 2.57/0.73    ~spl6_4 | spl6_19),
% 2.57/0.73    inference(avatar_split_clause,[],[f392,f396,f146])).
% 2.57/0.73  fof(f392,plain,(
% 2.57/0.73    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 2.57/0.73    inference(resolution,[],[f84,f74])).
% 2.57/0.73  fof(f310,plain,(
% 2.57/0.73    ~spl6_6 | spl6_11 | ~spl6_7),
% 2.57/0.73    inference(avatar_split_clause,[],[f305,f186,f308,f182])).
% 2.57/0.73  fof(f182,plain,(
% 2.57/0.73    spl6_6 <=> v1_relat_1(k1_xboole_0)),
% 2.57/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.57/0.73  fof(f186,plain,(
% 2.57/0.73    spl6_7 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 2.57/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.57/0.73  fof(f305,plain,(
% 2.57/0.73    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_7),
% 2.57/0.73    inference(superposition,[],[f95,f187])).
% 2.57/0.73  fof(f187,plain,(
% 2.57/0.73    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl6_7),
% 2.57/0.73    inference(avatar_component_clause,[],[f186])).
% 2.57/0.73  fof(f95,plain,(
% 2.57/0.73    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f40])).
% 2.57/0.73  fof(f40,plain,(
% 2.57/0.73    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.57/0.73    inference(ennf_transformation,[],[f11])).
% 2.57/0.73  fof(f11,axiom,(
% 2.57/0.73    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.57/0.73  fof(f206,plain,(
% 2.57/0.73    ~spl6_6 | spl6_8 | ~spl6_7),
% 2.57/0.73    inference(avatar_split_clause,[],[f201,f186,f204,f182])).
% 2.57/0.73  fof(f201,plain,(
% 2.57/0.73    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_7),
% 2.57/0.73    inference(superposition,[],[f94,f187])).
% 2.57/0.73  fof(f94,plain,(
% 2.57/0.73    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f39])).
% 2.57/0.73  fof(f39,plain,(
% 2.57/0.73    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.57/0.73    inference(ennf_transformation,[],[f12])).
% 2.57/0.73  fof(f12,axiom,(
% 2.57/0.73    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 2.57/0.73  fof(f200,plain,(
% 2.57/0.73    spl6_6),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f196])).
% 2.57/0.73  fof(f196,plain,(
% 2.57/0.73    $false | spl6_6),
% 2.57/0.73    inference(resolution,[],[f195,f160])).
% 2.57/0.73  fof(f195,plain,(
% 2.57/0.73    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl6_6),
% 2.57/0.73    inference(resolution,[],[f191,f106])).
% 2.57/0.73  fof(f191,plain,(
% 2.57/0.73    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl6_6),
% 2.57/0.73    inference(superposition,[],[f189,f125])).
% 2.57/0.73  fof(f189,plain,(
% 2.57/0.73    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_6),
% 2.57/0.73    inference(resolution,[],[f184,f111])).
% 2.57/0.73  fof(f111,plain,(
% 2.57/0.73    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/0.73    inference(cnf_transformation,[],[f46])).
% 2.57/0.73  fof(f46,plain,(
% 2.57/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/0.73    inference(ennf_transformation,[],[f17])).
% 2.57/0.73  fof(f17,axiom,(
% 2.57/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.57/0.73  fof(f184,plain,(
% 2.57/0.73    ~v1_relat_1(k1_xboole_0) | spl6_6),
% 2.57/0.73    inference(avatar_component_clause,[],[f182])).
% 2.57/0.73  fof(f188,plain,(
% 2.57/0.73    ~spl6_6 | spl6_7),
% 2.57/0.73    inference(avatar_split_clause,[],[f176,f186,f182])).
% 2.57/0.73  fof(f176,plain,(
% 2.57/0.73    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 2.57/0.73    inference(resolution,[],[f171,f93])).
% 2.57/0.73  fof(f93,plain,(
% 2.57/0.73    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f38])).
% 2.57/0.73  fof(f38,plain,(
% 2.57/0.73    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.57/0.73    inference(ennf_transformation,[],[f13])).
% 2.57/0.73  fof(f13,axiom,(
% 2.57/0.73    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.57/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 2.57/0.73  fof(f168,plain,(
% 2.57/0.73    spl6_4),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f164])).
% 2.57/0.73  fof(f164,plain,(
% 2.57/0.73    $false | spl6_4),
% 2.57/0.73    inference(resolution,[],[f163,f76])).
% 2.57/0.73  fof(f163,plain,(
% 2.57/0.73    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_4),
% 2.57/0.73    inference(resolution,[],[f111,f148])).
% 2.57/0.73  fof(f148,plain,(
% 2.57/0.73    ~v1_relat_1(sK3) | spl6_4),
% 2.57/0.73    inference(avatar_component_clause,[],[f146])).
% 2.57/0.73  fof(f155,plain,(
% 2.57/0.73    spl6_5),
% 2.57/0.73    inference(avatar_contradiction_clause,[],[f154])).
% 2.57/0.73  fof(f154,plain,(
% 2.57/0.73    $false | spl6_5),
% 2.57/0.73    inference(resolution,[],[f152,f74])).
% 2.57/0.73  fof(f152,plain,(
% 2.57/0.73    ~v1_funct_1(sK3) | spl6_5),
% 2.57/0.73    inference(avatar_component_clause,[],[f150])).
% 2.57/0.73  fof(f153,plain,(
% 2.57/0.73    ~spl6_4 | ~spl6_5 | spl6_1),
% 2.57/0.73    inference(avatar_split_clause,[],[f144,f129,f150,f146])).
% 2.57/0.73  fof(f144,plain,(
% 2.57/0.73    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_1),
% 2.57/0.73    inference(resolution,[],[f86,f131])).
% 2.57/0.73  fof(f131,plain,(
% 2.57/0.73    ~v1_funct_1(k2_funct_1(sK3)) | spl6_1),
% 2.57/0.73    inference(avatar_component_clause,[],[f129])).
% 2.57/0.73  fof(f86,plain,(
% 2.57/0.73    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.57/0.73    inference(cnf_transformation,[],[f33])).
% 2.57/0.73  fof(f140,plain,(
% 2.57/0.73    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 2.57/0.73    inference(avatar_split_clause,[],[f79,f137,f133,f129])).
% 2.57/0.73  fof(f79,plain,(
% 2.57/0.73    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 2.57/0.73    inference(cnf_transformation,[],[f57])).
% 2.57/0.73  % SZS output end Proof for theBenchmark
% 2.57/0.73  % (16227)------------------------------
% 2.57/0.73  % (16227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.57/0.73  % (16227)Termination reason: Refutation
% 2.57/0.73  
% 2.57/0.73  % (16227)Memory used [KB]: 6908
% 2.57/0.73  % (16227)Time elapsed: 0.282 s
% 2.57/0.73  % (16227)------------------------------
% 2.57/0.73  % (16227)------------------------------
% 2.57/0.73  % (16214)Success in time 0.363 s
%------------------------------------------------------------------------------
