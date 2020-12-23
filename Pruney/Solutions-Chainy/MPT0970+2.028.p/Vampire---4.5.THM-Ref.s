%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:52 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 199 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  259 ( 738 expanded)
%              Number of equality atoms :   56 ( 195 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f112,f132,f140,f144,f193,f215,f268,f349])).

fof(f349,plain,
    ( ~ spl6_2
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl6_2
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f52,f337,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f337,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),k1_xboole_0),k1_xboole_0)
    | ~ spl6_2
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f286,f291,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f291,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),k1_xboole_0),k2_relat_1(sK2))
    | ~ spl6_2
    | spl6_8 ),
    inference(backward_demodulation,[],[f191,f100])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f191,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_8
  <=> r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f286,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f87,f100])).

fof(f87,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f32,f61])).

fof(f61,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f31,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f32,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

% (14000)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f268,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f74,f192,f253,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f253,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f87,f192,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f192,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f74,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f62,f61])).

fof(f62,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f215,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f87,f188])).

fof(f188,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_7
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f193,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f179,f130,f190,f186])).

fof(f130,plain,
    ( spl6_6
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f179,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2)
    | ~ spl6_6 ),
    inference(factoring,[],[f149])).

fof(f149,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(X1,sK1),k2_relat_1(sK2))
        | r2_hidden(sK4(X1,sK1),X1)
        | sK1 = X1 )
    | ~ spl6_6 ),
    inference(resolution,[],[f146,f35])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f131,f27])).

fof(f27,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f144,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f29,f128])).

fof(f128,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f140,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f31,f124,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f132,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f113,f102,f130,f126,f122])).

fof(f102,plain,
    ( spl6_3
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f85,f104])).

fof(f104,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f85,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f37,f28])).

fof(f28,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f112,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f63,f96,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f96,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f63,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f43])).

fof(f105,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f68,f102,f98,f94])).

fof(f68,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f58,f60])).

fof(f60,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f30,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:40:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (13978)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (13981)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.57  % (13983)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.57  % (13979)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.57  % (13985)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.58  % (13981)Refutation found. Thanks to Tanya!
% 1.38/0.58  % SZS status Theorem for theBenchmark
% 1.66/0.59  % (13998)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.66/0.59  % (13990)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.66/0.59  % (13982)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.66/0.59  % (13988)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.66/0.59  % SZS output start Proof for theBenchmark
% 1.66/0.59  fof(f350,plain,(
% 1.66/0.59    $false),
% 1.66/0.59    inference(avatar_sat_refutation,[],[f105,f112,f132,f140,f144,f193,f215,f268,f349])).
% 1.66/0.59  fof(f349,plain,(
% 1.66/0.59    ~spl6_2 | spl6_8),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f346])).
% 1.66/0.59  fof(f346,plain,(
% 1.66/0.59    $false | (~spl6_2 | spl6_8)),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f52,f337,f38])).
% 1.66/0.59  fof(f38,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f21])).
% 1.66/0.59  fof(f21,plain,(
% 1.66/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f6])).
% 1.66/0.59  fof(f6,axiom,(
% 1.66/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.66/0.59  fof(f337,plain,(
% 1.66/0.59    r2_hidden(sK4(k2_relat_1(sK2),k1_xboole_0),k1_xboole_0) | (~spl6_2 | spl6_8)),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f286,f291,f35])).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f2])).
% 1.66/0.59  fof(f2,axiom,(
% 1.66/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.66/0.59  fof(f291,plain,(
% 1.66/0.59    ~r2_hidden(sK4(k2_relat_1(sK2),k1_xboole_0),k2_relat_1(sK2)) | (~spl6_2 | spl6_8)),
% 1.66/0.59    inference(backward_demodulation,[],[f191,f100])).
% 1.66/0.59  fof(f100,plain,(
% 1.66/0.59    k1_xboole_0 = sK1 | ~spl6_2),
% 1.66/0.59    inference(avatar_component_clause,[],[f98])).
% 1.66/0.59  fof(f98,plain,(
% 1.66/0.59    spl6_2 <=> k1_xboole_0 = sK1),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.66/0.59  fof(f191,plain,(
% 1.66/0.59    ~r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | spl6_8),
% 1.66/0.59    inference(avatar_component_clause,[],[f190])).
% 1.66/0.59  fof(f190,plain,(
% 1.66/0.59    spl6_8 <=> r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.66/0.59  fof(f286,plain,(
% 1.66/0.59    k1_xboole_0 != k2_relat_1(sK2) | ~spl6_2),
% 1.66/0.59    inference(backward_demodulation,[],[f87,f100])).
% 1.66/0.59  fof(f87,plain,(
% 1.66/0.59    sK1 != k2_relat_1(sK2)),
% 1.66/0.59    inference(superposition,[],[f32,f61])).
% 1.66/0.59  fof(f61,plain,(
% 1.66/0.59    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f31,f34])).
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f17])).
% 1.66/0.59  fof(f17,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.66/0.59  fof(f31,plain,(
% 1.66/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.59    inference(cnf_transformation,[],[f15])).
% 1.66/0.59  fof(f15,plain,(
% 1.66/0.59    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.66/0.59    inference(flattening,[],[f14])).
% 1.66/0.59  fof(f14,plain,(
% 1.66/0.59    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.66/0.59    inference(ennf_transformation,[],[f13])).
% 1.66/0.59  fof(f13,negated_conjecture,(
% 1.66/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.66/0.59    inference(negated_conjecture,[],[f12])).
% 1.66/0.59  fof(f12,conjecture,(
% 1.66/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.66/0.59  fof(f32,plain,(
% 1.66/0.59    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.66/0.59    inference(cnf_transformation,[],[f15])).
% 1.66/0.59  % (14000)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.66/0.59  fof(f52,plain,(
% 1.66/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f3])).
% 1.66/0.59  fof(f3,axiom,(
% 1.66/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.66/0.59  fof(f268,plain,(
% 1.66/0.59    ~spl6_8),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f264])).
% 1.66/0.59  fof(f264,plain,(
% 1.66/0.59    $false | ~spl6_8),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f74,f192,f253,f39])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f22])).
% 1.66/0.59  fof(f22,plain,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.66/0.59    inference(ennf_transformation,[],[f1])).
% 1.66/0.59  fof(f1,axiom,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.66/0.59  fof(f253,plain,(
% 1.66/0.59    ~r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1) | ~spl6_8),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f87,f192,f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f192,plain,(
% 1.66/0.59    r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | ~spl6_8),
% 1.66/0.59    inference(avatar_component_clause,[],[f190])).
% 1.66/0.59  fof(f74,plain,(
% 1.66/0.59    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f67,f43])).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f4])).
% 1.66/0.59  fof(f4,axiom,(
% 1.66/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.66/0.59  fof(f67,plain,(
% 1.66/0.59    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.66/0.59    inference(backward_demodulation,[],[f62,f61])).
% 1.66/0.59  fof(f62,plain,(
% 1.66/0.59    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f31,f33])).
% 1.66/0.59  fof(f33,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f16,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.66/0.59  fof(f215,plain,(
% 1.66/0.59    ~spl6_7),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f210])).
% 1.66/0.59  fof(f210,plain,(
% 1.66/0.59    $false | ~spl6_7),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f87,f188])).
% 1.66/0.59  fof(f188,plain,(
% 1.66/0.59    sK1 = k2_relat_1(sK2) | ~spl6_7),
% 1.66/0.59    inference(avatar_component_clause,[],[f186])).
% 1.66/0.59  fof(f186,plain,(
% 1.66/0.59    spl6_7 <=> sK1 = k2_relat_1(sK2)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.66/0.59  fof(f193,plain,(
% 1.66/0.59    spl6_7 | spl6_8 | ~spl6_6),
% 1.66/0.59    inference(avatar_split_clause,[],[f179,f130,f190,f186])).
% 1.66/0.59  fof(f130,plain,(
% 1.66/0.59    spl6_6 <=> ! [X0] : (~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2)))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.66/0.59  fof(f179,plain,(
% 1.66/0.59    r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2) | ~spl6_6),
% 1.66/0.59    inference(factoring,[],[f149])).
% 1.66/0.59  fof(f149,plain,(
% 1.66/0.59    ( ! [X1] : (r2_hidden(sK4(X1,sK1),k2_relat_1(sK2)) | r2_hidden(sK4(X1,sK1),X1) | sK1 = X1) ) | ~spl6_6),
% 1.66/0.59    inference(resolution,[],[f146,f35])).
% 1.66/0.59  fof(f146,plain,(
% 1.66/0.59    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl6_6),
% 1.66/0.59    inference(duplicate_literal_removal,[],[f145])).
% 1.66/0.59  fof(f145,plain,(
% 1.66/0.59    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,sK1)) ) | ~spl6_6),
% 1.66/0.59    inference(resolution,[],[f131,f27])).
% 1.66/0.59  fof(f27,plain,(
% 1.66/0.59    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f15])).
% 1.66/0.59  fof(f131,plain,(
% 1.66/0.59    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl6_6),
% 1.66/0.59    inference(avatar_component_clause,[],[f130])).
% 1.66/0.59  fof(f144,plain,(
% 1.66/0.59    spl6_5),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f141])).
% 1.66/0.59  fof(f141,plain,(
% 1.66/0.59    $false | spl6_5),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f29,f128])).
% 1.66/0.59  fof(f128,plain,(
% 1.66/0.59    ~v1_funct_1(sK2) | spl6_5),
% 1.66/0.59    inference(avatar_component_clause,[],[f126])).
% 1.66/0.59  fof(f126,plain,(
% 1.66/0.59    spl6_5 <=> v1_funct_1(sK2)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.66/0.59  fof(f29,plain,(
% 1.66/0.59    v1_funct_1(sK2)),
% 1.66/0.59    inference(cnf_transformation,[],[f15])).
% 1.66/0.59  fof(f140,plain,(
% 1.66/0.59    spl6_4),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f135])).
% 1.66/0.59  fof(f135,plain,(
% 1.66/0.59    $false | spl6_4),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f31,f124,f51])).
% 1.66/0.59  fof(f51,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f7])).
% 1.66/0.59  fof(f7,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.66/0.59  fof(f124,plain,(
% 1.66/0.59    ~v1_relat_1(sK2) | spl6_4),
% 1.66/0.59    inference(avatar_component_clause,[],[f122])).
% 1.66/0.59  fof(f122,plain,(
% 1.66/0.59    spl6_4 <=> v1_relat_1(sK2)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.66/0.59  fof(f132,plain,(
% 1.66/0.59    ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_3),
% 1.66/0.59    inference(avatar_split_clause,[],[f113,f102,f130,f126,f122])).
% 1.66/0.59  fof(f102,plain,(
% 1.66/0.59    spl6_3 <=> sK0 = k1_relat_1(sK2)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.66/0.59  fof(f113,plain,(
% 1.66/0.59    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 1.66/0.59    inference(backward_demodulation,[],[f85,f104])).
% 1.66/0.59  fof(f104,plain,(
% 1.66/0.59    sK0 = k1_relat_1(sK2) | ~spl6_3),
% 1.66/0.59    inference(avatar_component_clause,[],[f102])).
% 1.66/0.59  fof(f85,plain,(
% 1.66/0.59    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(X0),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 1.66/0.59    inference(superposition,[],[f37,f28])).
% 1.66/0.59  fof(f28,plain,(
% 1.66/0.59    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f15])).
% 1.66/0.59  fof(f37,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f20])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(flattening,[],[f19])).
% 1.66/0.59  fof(f19,plain,(
% 1.66/0.59    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f5])).
% 1.66/0.59  fof(f5,axiom,(
% 1.66/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.66/0.59  fof(f112,plain,(
% 1.66/0.59    spl6_1),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f108])).
% 1.66/0.59  fof(f108,plain,(
% 1.66/0.59    $false | spl6_1),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f63,f96,f42])).
% 1.66/0.59  fof(f42,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f4])).
% 1.66/0.59  fof(f96,plain,(
% 1.66/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_1),
% 1.66/0.59    inference(avatar_component_clause,[],[f94])).
% 1.66/0.59  fof(f94,plain,(
% 1.66/0.59    spl6_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.66/0.59  fof(f63,plain,(
% 1.66/0.59    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f31,f43])).
% 1.66/0.59  fof(f105,plain,(
% 1.66/0.59    ~spl6_1 | spl6_2 | spl6_3),
% 1.66/0.59    inference(avatar_split_clause,[],[f68,f102,f98,f94])).
% 1.66/0.59  fof(f68,plain,(
% 1.66/0.59    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.59    inference(backward_demodulation,[],[f58,f60])).
% 1.66/0.59  fof(f60,plain,(
% 1.66/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f31,f50])).
% 1.66/0.59  fof(f50,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f25])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.66/0.59  fof(f58,plain,(
% 1.66/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.59    inference(resolution,[],[f30,f49])).
% 1.66/0.59  fof(f49,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f24,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(flattening,[],[f23])).
% 1.66/0.59  fof(f23,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.66/0.59  fof(f30,plain,(
% 1.66/0.59    v1_funct_2(sK2,sK0,sK1)),
% 1.66/0.59    inference(cnf_transformation,[],[f15])).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (13981)------------------------------
% 1.66/0.59  % (13981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (13981)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (13981)Memory used [KB]: 6268
% 1.66/0.59  % (13981)Time elapsed: 0.147 s
% 1.66/0.59  % (13981)------------------------------
% 1.66/0.59  % (13981)------------------------------
% 1.66/0.59  % (13980)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.66/0.59  % (13992)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.66/0.59  % (13995)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.66/0.59  % (13976)Success in time 0.231 s
%------------------------------------------------------------------------------
