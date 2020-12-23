%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 171 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   24
%              Number of atoms          :  307 ( 512 expanded)
%              Number of equality atoms :   74 ( 131 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f83,f99,f106,f121,f137,f152,f189,f228])).

fof(f228,plain,
    ( ~ spl6_7
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl6_7
    | spl6_14 ),
    inference(subsumption_resolution,[],[f223,f188])).

fof(f188,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_14
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f223,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_7 ),
    inference(resolution,[],[f216,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f216,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(X3) )
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f212,f54])).

fof(f54,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

% (27716)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

% (27712)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f212,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k1_relat_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl6_7 ),
    inference(superposition,[],[f208,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f208,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f205,f54])).

fof(f205,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl6_7 ),
    inference(resolution,[],[f192,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl6_7 ),
    inference(condensation,[],[f191])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl6_7 ),
    inference(resolution,[],[f163,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X1,X2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
    | ~ spl6_7 ),
    inference(resolution,[],[f141,f40])).

fof(f141,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X0,X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f140,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f140,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) )
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f139,f53])).

fof(f139,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
        | ~ r2_hidden(X0,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) )
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f138,f35])).

fof(f138,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
        | ~ r2_hidden(X0,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) )
    | ~ spl6_7 ),
    inference(resolution,[],[f128,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f128,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ r2_hidden(sK5(X3,X4,X2),k1_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X3,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f85,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_7
  <=> k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f85,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ r2_hidden(sK5(X3,X4,X2),k2_relset_1(sK0,sK1,sK2))
      | ~ r2_hidden(X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ) ),
    inference(resolution,[],[f77,f52])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | ~ r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f30,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

% (27702)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f30,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f189,plain,
    ( ~ spl6_14
    | spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f169,f130,f80,f186])).

fof(f80,plain,
    ( spl6_5
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f130,plain,
    ( spl6_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f169,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl6_5
    | ~ spl6_9 ),
    inference(superposition,[],[f82,f132])).

fof(f132,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f82,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f152,plain,
    ( ~ spl6_3
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl6_3
    | spl6_10 ),
    inference(resolution,[],[f143,f68])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f143,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_10 ),
    inference(resolution,[],[f136,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f137,plain,
    ( spl6_9
    | ~ spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f125,f118,f134,f130])).

fof(f118,plain,
    ( spl6_8
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(superposition,[],[f37,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f121,plain,
    ( spl6_8
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f112,f96,f66,f118])).

fof(f112,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f108,f68])).

fof(f108,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(superposition,[],[f98,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f106,plain,
    ( ~ spl6_3
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl6_3
    | spl6_6 ),
    inference(subsumption_resolution,[],[f102,f68])).

fof(f102,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_6 ),
    inference(resolution,[],[f94,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f94,plain,
    ( ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_6
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f99,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f89,f96,f92])).

fof(f89,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f78,f40])).

fof(f78,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3(sK1,X2),k2_relset_1(sK0,sK1,sK2))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,
    ( ~ spl6_5
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f76,f71,f66,f80])).

fof(f71,plain,
    ( spl6_4
  <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f76,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f75,f68])).

fof(f75,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_4 ),
    inference(superposition,[],[f73,f46])).

fof(f73,plain,
    ( k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f74,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:24:00 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.48  % (27708)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (27701)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (27704)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (27701)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f69,f74,f83,f99,f106,f121,f137,f152,f189,f228])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    ~spl6_7 | spl6_14),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    $false | (~spl6_7 | spl6_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f223,f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl6_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl6_14 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_7),
% 0.21/0.48    inference(resolution,[],[f216,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3)) ) | ~spl6_7),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f215])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_7),
% 0.21/0.48    inference(forward_demodulation,[],[f212,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f42])).
% 0.21/0.48  % (27716)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  % (27712)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) ) | ~spl6_7),
% 0.21/0.48    inference(superposition,[],[f208,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_7),
% 0.21/0.48    inference(forward_demodulation,[],[f205,f54])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) ) | ~spl6_7),
% 0.21/0.48    inference(resolution,[],[f192,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl6_7),
% 0.21/0.48    inference(condensation,[],[f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl6_7),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl6_7),
% 0.21/0.48    inference(resolution,[],[f163,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X1,X2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) ) | ~spl6_7),
% 0.21/0.48    inference(resolution,[],[f141,f40])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X0,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_7),
% 0.21/0.48    inference(forward_demodulation,[],[f140,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))) ) | ~spl6_7),
% 0.21/0.48    inference(forward_demodulation,[],[f139,f53])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))) ) | ~spl6_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f35])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))) ) | ~spl6_7),
% 0.21/0.48    inference(resolution,[],[f128,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK5(X3,X4,X2),k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~r2_hidden(X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))) ) | ~spl6_7),
% 0.21/0.48    inference(forward_demodulation,[],[f85,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl6_7 <=> k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X4,X2,X5,X3] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~r2_hidden(sK5(X3,X4,X2),k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))) )),
% 0.21/0.48    inference(resolution,[],[f77,f52])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))) )),
% 0.21/0.48    inference(resolution,[],[f30,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.48  % (27702)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~spl6_14 | spl6_5 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f169,f130,f80,f186])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl6_5 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl6_9 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (spl6_5 | ~spl6_9)),
% 0.21/0.48    inference(superposition,[],[f82,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl6_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f130])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(sK2) | spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ~spl6_3 | spl6_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    $false | (~spl6_3 | spl6_10)),
% 0.21/0.48    inference(resolution,[],[f143,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_10),
% 0.21/0.48    inference(resolution,[],[f136,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl6_10 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    spl6_9 | ~spl6_10 | ~spl6_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f125,f118,f134,f130])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    spl6_8 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl6_8),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl6_8),
% 0.21/0.48    inference(superposition,[],[f37,f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK2) | ~spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f118])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl6_8 | ~spl6_3 | ~spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f112,f96,f66,f118])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK2) | (~spl6_3 | ~spl6_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f68])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.21/0.48    inference(superposition,[],[f98,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~spl6_3 | spl6_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    $false | (~spl6_3 | spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f68])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_6),
% 0.21/0.48    inference(resolution,[],[f94,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl6_6 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ~spl6_6 | spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f89,f96,f92])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.48    inference(resolution,[],[f78,f40])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(sK3(sK1,X2),k2_relset_1(sK0,sK1,sK2)) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(sK1))) )),
% 0.21/0.48    inference(resolution,[],[f30,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~spl6_5 | ~spl6_3 | spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f76,f71,f66,f80])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl6_4 <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(sK2) | (~spl6_3 | spl6_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f75,f68])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_4),
% 0.21/0.48    inference(superposition,[],[f73,f46])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) | spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f71])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f66])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27701)------------------------------
% 0.21/0.48  % (27701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27701)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27701)Memory used [KB]: 10746
% 0.21/0.48  % (27701)Time elapsed: 0.067 s
% 0.21/0.48  % (27701)------------------------------
% 0.21/0.48  % (27701)------------------------------
% 0.21/0.48  % (27703)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (27697)Success in time 0.128 s
%------------------------------------------------------------------------------
