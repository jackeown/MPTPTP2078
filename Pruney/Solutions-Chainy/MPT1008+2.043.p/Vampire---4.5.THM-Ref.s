%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 165 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  366 ( 531 expanded)
%              Number of equality atoms :  126 ( 180 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f299,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f107,f114,f121,f128,f133,f152,f187,f220,f297,f298])).

fof(f298,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | k1_xboole_0 != k1_relat_1(sK2)
    | k1_tarski(sK0) = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f297,plain,
    ( ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | spl6_13 ),
    inference(subsumption_resolution,[],[f294,f201])).

fof(f201,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_13
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f294,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f249,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

% (10189)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f249,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_tarski(sK0))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f241,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f241,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k4_tarski(X2,sK5(k1_xboole_0,X2)))
        | ~ r2_hidden(X2,k1_tarski(sK0)) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f141,f230])).

fof(f230,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f227,f120])).

fof(f120,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f227,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_9 ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_9 ),
    inference(superposition,[],[f46,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_9
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

% (10190)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f141,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,k4_tarski(X2,sK5(sK2,X2)))
        | ~ r2_hidden(X2,k1_tarski(sK0)) )
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(resolution,[],[f139,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f139,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f138,f106])).

fof(f106,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
        | ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) )
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) != k1_tarski(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
        | ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) )
    | ~ spl6_8 ),
    inference(superposition,[],[f69,f132])).

fof(f132,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_8
  <=> k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

% (10207)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f220,plain,
    ( ~ spl6_1
    | ~ spl6_6
    | spl6_7
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | spl6_7
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f218,f127])).

fof(f127,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_7
  <=> k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f218,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(equality_resolution,[],[f191])).

fof(f191,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0)) )
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f190,f120])).

fof(f190,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | ~ v1_relat_1(sK2)
        | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0)) )
    | ~ spl6_1
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f188,f88])).

fof(f88,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f188,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0)) )
    | ~ spl6_11 ),
    inference(superposition,[],[f54,f186])).

fof(f186,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_11
  <=> k1_tarski(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f187,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f166,f150,f104,f184])).

fof(f150,plain,
    ( spl6_10
  <=> ! [X1,X0] :
        ( ~ v4_relat_1(sK2,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_relat_1(sK2)
        | k1_tarski(X1) = k1_relat_1(sK2)
        | k1_tarski(X0) = k1_relat_1(sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f166,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(resolution,[],[f159,f106])).

fof(f159,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2)))
        | k1_tarski(X1) = k1_relat_1(sK2) )
    | ~ spl6_10 ),
    inference(resolution,[],[f157,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,k1_tarski(X0))
        | k1_tarski(X0) = k1_relat_1(sK2) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,k1_tarski(X0))
        | k1_tarski(X0) = k1_relat_1(sK2)
        | k1_tarski(X0) = k1_relat_1(sK2)
        | k1_tarski(X0) = k1_relat_1(sK2) )
    | ~ spl6_10 ),
    inference(superposition,[],[f151,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_relat_1(sK2)
        | k1_tarski(X1) = k1_relat_1(sK2)
        | k1_tarski(X0) = k1_relat_1(sK2) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f134,f118,f150,f146])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,k2_tarski(X0,X1))
        | k1_tarski(X0) = k1_relat_1(sK2)
        | k1_tarski(X1) = k1_relat_1(sK2)
        | k2_tarski(X0,X1) = k1_relat_1(sK2)
        | k1_xboole_0 = k1_relat_1(sK2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f123,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f123,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(sK2),X1)
        | ~ v4_relat_1(sK2,X1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f120,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f133,plain,
    ( spl6_8
    | spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f102,f96,f91,f130])).

fof(f91,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f96,plain,
    ( spl6_3
  <=> v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f102,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f101,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f101,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f100,f93])).

fof(f93,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl6_3 ),
    inference(resolution,[],[f98,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f98,plain,
    ( v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f128,plain,
    ( ~ spl6_7
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f116,f111,f104,f125])).

fof(f111,plain,
    ( spl6_5
  <=> k2_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f116,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f115,f106])).

fof(f115,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | spl6_5 ),
    inference(superposition,[],[f113,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f113,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f121,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f108,f104,f118])).

fof(f108,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f106,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f42,f111])).

fof(f42,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f40,f104])).

fof(f99,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (10188)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (10203)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (10188)Refutation not found, incomplete strategy% (10188)------------------------------
% 0.20/0.51  % (10188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10192)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (10195)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (10198)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (10188)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10188)Memory used [KB]: 6396
% 0.20/0.53  % (10188)Time elapsed: 0.100 s
% 0.20/0.53  % (10188)------------------------------
% 0.20/0.53  % (10188)------------------------------
% 0.20/0.53  % (10205)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (10185)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (10206)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (10186)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (10183)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (10184)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (10203)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f299,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f89,f94,f99,f107,f114,f121,f128,f133,f152,f187,f220,f297,f298])).
% 0.20/0.53  fof(f298,plain,(
% 0.20/0.53    k1_xboole_0 != k1_tarski(sK0) | k1_xboole_0 != k1_relat_1(sK2) | k1_tarski(sK0) = k1_relat_1(sK2)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f297,plain,(
% 0.20/0.53    ~spl6_4 | ~spl6_6 | ~spl6_8 | ~spl6_9 | spl6_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f296])).
% 0.20/0.53  fof(f296,plain,(
% 0.20/0.53    $false | (~spl6_4 | ~spl6_6 | ~spl6_8 | ~spl6_9 | spl6_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f294,f201])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    k1_xboole_0 != k1_tarski(sK0) | spl6_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f199])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    spl6_13 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tarski(sK0) | (~spl6_4 | ~spl6_6 | ~spl6_8 | ~spl6_9)),
% 0.20/0.53    inference(resolution,[],[f249,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  % (10189)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK0))) ) | (~spl6_4 | ~spl6_6 | ~spl6_8 | ~spl6_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f241,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    ( ! [X2] : (~r1_tarski(k1_xboole_0,k4_tarski(X2,sK5(k1_xboole_0,X2))) | ~r2_hidden(X2,k1_tarski(sK0))) ) | (~spl6_4 | ~spl6_6 | ~spl6_8 | ~spl6_9)),
% 0.20/0.53    inference(backward_demodulation,[],[f141,f230])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | (~spl6_6 | ~spl6_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f227,f120])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    v1_relat_1(sK2) | ~spl6_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    spl6_6 <=> v1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl6_9),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f226])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl6_9),
% 0.20/0.53    inference(superposition,[],[f46,f148])).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(sK2) | ~spl6_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f146])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    spl6_9 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  % (10190)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ( ! [X2] : (~r1_tarski(sK2,k4_tarski(X2,sK5(sK2,X2))) | ~r2_hidden(X2,k1_tarski(sK0))) ) | (~spl6_4 | ~spl6_8)),
% 0.20/0.53    inference(resolution,[],[f139,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) | ~r2_hidden(X0,k1_tarski(sK0))) ) | (~spl6_4 | ~spl6_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f138,f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl6_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    spl6_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)) ) | ~spl6_8),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(sK0) != k1_tarski(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)) ) | ~spl6_8),
% 0.20/0.53    inference(superposition,[],[f69,f132])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) | ~spl6_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f130])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    spl6_8 <=> k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.53  % (10207)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  fof(f220,plain,(
% 0.20/0.53    ~spl6_1 | ~spl6_6 | spl6_7 | ~spl6_11),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f219])).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    $false | (~spl6_1 | ~spl6_6 | spl6_7 | ~spl6_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f218,f127])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | spl6_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f125])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    spl6_7 <=> k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | (~spl6_1 | ~spl6_6 | ~spl6_11)),
% 0.20/0.53    inference(equality_resolution,[],[f191])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0))) ) | (~spl6_1 | ~spl6_6 | ~spl6_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f190,f120])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0))) ) | (~spl6_1 | ~spl6_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f188,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    v1_funct_1(sK2) | ~spl6_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    spl6_1 <=> v1_funct_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0))) ) | ~spl6_11),
% 0.20/0.53    inference(superposition,[],[f54,f186])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    k1_tarski(sK0) = k1_relat_1(sK2) | ~spl6_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f184])).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    spl6_11 <=> k1_tarski(sK0) = k1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    spl6_11 | ~spl6_4 | ~spl6_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f166,f150,f104,f184])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    spl6_10 <=> ! [X1,X0] : (~v4_relat_1(sK2,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_relat_1(sK2) | k1_tarski(X1) = k1_relat_1(sK2) | k1_tarski(X0) = k1_relat_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    k1_tarski(sK0) = k1_relat_1(sK2) | (~spl6_4 | ~spl6_10)),
% 0.20/0.53    inference(resolution,[],[f159,f106])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) | k1_tarski(X1) = k1_relat_1(sK2)) ) | ~spl6_10),
% 0.20/0.53    inference(resolution,[],[f157,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    ( ! [X0] : (~v4_relat_1(sK2,k1_tarski(X0)) | k1_tarski(X0) = k1_relat_1(sK2)) ) | ~spl6_10),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f156])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    ( ! [X0] : (~v4_relat_1(sK2,k1_tarski(X0)) | k1_tarski(X0) = k1_relat_1(sK2) | k1_tarski(X0) = k1_relat_1(sK2) | k1_tarski(X0) = k1_relat_1(sK2)) ) | ~spl6_10),
% 0.20/0.53    inference(superposition,[],[f151,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v4_relat_1(sK2,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_relat_1(sK2) | k1_tarski(X1) = k1_relat_1(sK2) | k1_tarski(X0) = k1_relat_1(sK2)) ) | ~spl6_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f150])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    spl6_9 | spl6_10 | ~spl6_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f134,f118,f150,f146])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v4_relat_1(sK2,k2_tarski(X0,X1)) | k1_tarski(X0) = k1_relat_1(sK2) | k1_tarski(X1) = k1_relat_1(sK2) | k2_tarski(X0,X1) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)) ) | ~spl6_6),
% 0.20/0.53    inference(resolution,[],[f123,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(k1_relat_1(sK2),X1) | ~v4_relat_1(sK2,X1)) ) | ~spl6_6),
% 0.20/0.53    inference(resolution,[],[f120,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    spl6_8 | spl6_2 | ~spl6_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f102,f96,f91,f130])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl6_2 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    spl6_3 <=> v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) | (spl6_2 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f101,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.20/0.53    inference(negated_conjecture,[],[f18])).
% 0.20/0.53  fof(f18,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | (spl6_2 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f100,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | spl6_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f91])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f98,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~spl6_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f96])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ~spl6_7 | ~spl6_4 | spl6_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f116,f111,f104,f125])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl6_5 <=> k2_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(k1_funct_1(sK2,sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | (~spl6_4 | spl6_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f115,f106])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | spl6_5),
% 0.20/0.53    inference(superposition,[],[f113,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) | spl6_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f111])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    spl6_6 | ~spl6_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f108,f104,f118])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    v1_relat_1(sK2) | ~spl6_4),
% 0.20/0.53    inference(resolution,[],[f106,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ~spl6_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f42,f111])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl6_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f40,f104])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl6_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f39,f96])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ~spl6_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f41,f91])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    k1_xboole_0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl6_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f38,f86])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (10203)------------------------------
% 0.20/0.53  % (10203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10203)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (10203)Memory used [KB]: 10874
% 0.20/0.53  % (10203)Time elapsed: 0.117 s
% 0.20/0.53  % (10203)------------------------------
% 0.20/0.53  % (10203)------------------------------
% 0.20/0.53  % (10187)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (10182)Success in time 0.177 s
%------------------------------------------------------------------------------
