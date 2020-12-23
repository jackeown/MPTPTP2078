%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 471 expanded)
%              Number of leaves         :   21 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          :  295 (1680 expanded)
%              Number of equality atoms :   48 ( 225 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5082)Memory used [KB]: 1791
% (5082)Time elapsed: 0.141 s
% (5082)------------------------------
% (5082)------------------------------
fof(f483,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f119,f140,f193,f228,f232,f240,f383,f482])).

fof(f482,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f34,f106])).

fof(f106,plain,
    ( ~ v1_funct_1(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f383,plain,
    ( spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f309,f306,f307,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f307,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f270,f298])).

fof(f298,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f226,f261,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f261,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f226,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f226,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f270,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f170,f259])).

fof(f259,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f219,f226,f55])).

fof(f219,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f170,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f82,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK0
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f102,f75,f82,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(unit_resulting_resolution,[],[f33,f66,f35,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f35,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f82,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f75,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f306,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f269,f298])).

fof(f269,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f167,f259])).

fof(f167,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | spl4_2 ),
    inference(backward_demodulation,[],[f75,f165])).

fof(f309,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f273,f298])).

fof(f273,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f176,f259])).

fof(f176,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl4_2 ),
    inference(backward_demodulation,[],[f102,f165])).

fof(f240,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f68,f66,f227,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f227,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f225])).

fof(f68,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f232,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f33,f223])).

fof(f223,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f228,plain,
    ( spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f209,f133,f100,f225,f221,f217])).

fof(f133,plain,
    ( spl4_4
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f209,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK1)
    | spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f54,f195])).

fof(f195,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f135,f165])).

fof(f135,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f193,plain,
    ( spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl4_2
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f68,f66,f181,f60])).

fof(f181,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f145,f165])).

fof(f145,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f141,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f141,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f139,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f139,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_5
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f140,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f77,f137,f133])).

fof(f77,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f35,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f119,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f83,f98,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f98,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f83,plain,(
    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f107,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f32,f104,f100,f96])).

fof(f32,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:09 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.22/0.50  % (5079)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (5071)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (5086)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (5064)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (5084)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (5069)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (5076)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (5065)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (5063)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (5061)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (5068)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (5062)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (5075)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (5066)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (5067)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (5070)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (5065)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (5088)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (5085)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (5083)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (5074)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (5087)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (5077)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (5089)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (5082)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (5083)Refutation not found, incomplete strategy% (5083)------------------------------
% 0.22/0.54  % (5083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5083)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5083)Memory used [KB]: 10874
% 0.22/0.54  % (5083)Time elapsed: 0.126 s
% 0.22/0.54  % (5083)------------------------------
% 0.22/0.54  % (5083)------------------------------
% 0.22/0.54  % (5071)Refutation not found, incomplete strategy% (5071)------------------------------
% 0.22/0.54  % (5071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5071)Memory used [KB]: 10746
% 0.22/0.54  % (5071)Time elapsed: 0.128 s
% 0.22/0.54  % (5071)------------------------------
% 0.22/0.54  % (5071)------------------------------
% 0.22/0.54  % (5073)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (5069)Refutation not found, incomplete strategy% (5069)------------------------------
% 0.22/0.54  % (5069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5072)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (5078)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (5063)Refutation not found, incomplete strategy% (5063)------------------------------
% 0.22/0.55  % (5063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5063)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5063)Memory used [KB]: 10746
% 0.22/0.55  % (5063)Time elapsed: 0.114 s
% 0.22/0.55  % (5063)------------------------------
% 0.22/0.55  % (5063)------------------------------
% 0.22/0.55  % (5090)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (5078)Refutation not found, incomplete strategy% (5078)------------------------------
% 0.22/0.55  % (5078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5078)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5078)Memory used [KB]: 10746
% 0.22/0.55  % (5078)Time elapsed: 0.133 s
% 0.22/0.55  % (5078)------------------------------
% 0.22/0.55  % (5078)------------------------------
% 0.22/0.55  % (5069)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5069)Memory used [KB]: 10874
% 0.22/0.55  % (5069)Time elapsed: 0.125 s
% 0.22/0.55  % (5069)------------------------------
% 0.22/0.55  % (5069)------------------------------
% 0.22/0.55  % (5080)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (5082)Refutation not found, incomplete strategy% (5082)------------------------------
% 0.22/0.56  % (5082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5081)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.56  % (5081)Refutation not found, incomplete strategy% (5081)------------------------------
% 1.56/0.56  % (5081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (5082)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  
% 1.56/0.56  % (5082)Memory used [KB]: 1791
% 1.56/0.56  % (5082)Time elapsed: 0.141 s
% 1.56/0.56  % (5082)------------------------------
% 1.56/0.56  % (5082)------------------------------
% 1.56/0.56  fof(f483,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(avatar_sat_refutation,[],[f107,f119,f140,f193,f228,f232,f240,f383,f482])).
% 1.56/0.56  fof(f482,plain,(
% 1.56/0.56    spl4_3),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f479])).
% 1.56/0.56  fof(f479,plain,(
% 1.56/0.56    $false | spl4_3),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f34,f106])).
% 1.56/0.56  fof(f106,plain,(
% 1.56/0.56    ~v1_funct_1(sK1) | spl4_3),
% 1.56/0.56    inference(avatar_component_clause,[],[f104])).
% 1.56/0.56  fof(f104,plain,(
% 1.56/0.56    spl4_3 <=> v1_funct_1(sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.56/0.56  fof(f34,plain,(
% 1.56/0.56    v1_funct_1(sK1)),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  fof(f17,plain,(
% 1.56/0.56    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.56/0.56    inference(flattening,[],[f16])).
% 1.56/0.56  fof(f16,plain,(
% 1.56/0.56    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.56/0.56    inference(ennf_transformation,[],[f15])).
% 1.56/0.56  fof(f15,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.56/0.56    inference(negated_conjecture,[],[f14])).
% 1.56/0.56  fof(f14,conjecture,(
% 1.56/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.56/0.56  fof(f383,plain,(
% 1.56/0.56    spl4_2 | ~spl4_6 | ~spl4_8),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f379])).
% 1.56/0.56  fof(f379,plain,(
% 1.56/0.56    $false | (spl4_2 | ~spl4_6 | ~spl4_8)),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f309,f306,f307,f62])).
% 1.56/0.56  fof(f62,plain,(
% 1.56/0.56    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.56/0.56    inference(equality_resolution,[],[f42])).
% 1.56/0.56  fof(f42,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f22])).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.56    inference(flattening,[],[f21])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.56    inference(ennf_transformation,[],[f13])).
% 1.56/0.56  fof(f13,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.56/0.56  fof(f307,plain,(
% 1.56/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_6 | ~spl4_8)),
% 1.56/0.56    inference(backward_demodulation,[],[f270,f298])).
% 1.56/0.56  fof(f298,plain,(
% 1.56/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_8),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f226,f261,f55])).
% 1.56/0.56  fof(f55,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f28])).
% 1.56/0.56  fof(f28,plain,(
% 1.56/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.56/0.56    inference(ennf_transformation,[],[f6])).
% 1.56/0.56  fof(f6,axiom,(
% 1.56/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.56/0.56  fof(f261,plain,(
% 1.56/0.56    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl4_8),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f226,f47])).
% 1.56/0.56  fof(f47,plain,(
% 1.56/0.56    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f24])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.56/0.56    inference(ennf_transformation,[],[f9])).
% 1.56/0.56  fof(f9,axiom,(
% 1.56/0.56    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.56/0.56  fof(f226,plain,(
% 1.56/0.56    v1_xboole_0(k1_xboole_0) | ~spl4_8),
% 1.56/0.56    inference(avatar_component_clause,[],[f225])).
% 1.56/0.56  fof(f225,plain,(
% 1.56/0.56    spl4_8 <=> v1_xboole_0(k1_xboole_0)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.56/0.56  fof(f270,plain,(
% 1.56/0.56    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_6 | ~spl4_8)),
% 1.56/0.56    inference(backward_demodulation,[],[f170,f259])).
% 1.56/0.56  fof(f259,plain,(
% 1.56/0.56    k1_xboole_0 = sK1 | (~spl4_6 | ~spl4_8)),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f219,f226,f55])).
% 1.56/0.56  fof(f219,plain,(
% 1.56/0.56    v1_xboole_0(sK1) | ~spl4_6),
% 1.56/0.56    inference(avatar_component_clause,[],[f217])).
% 1.56/0.56  fof(f217,plain,(
% 1.56/0.56    spl4_6 <=> v1_xboole_0(sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.56/0.56  fof(f170,plain,(
% 1.56/0.56    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | spl4_2),
% 1.56/0.56    inference(backward_demodulation,[],[f82,f165])).
% 1.56/0.56  fof(f165,plain,(
% 1.56/0.56    k1_xboole_0 = sK0 | spl4_2),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f102,f75,f82,f44])).
% 1.56/0.56  fof(f44,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f22])).
% 1.56/0.56  fof(f75,plain,(
% 1.56/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f33,f66,f35,f37])).
% 1.56/0.56  fof(f37,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f20])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.56/0.56    inference(flattening,[],[f19])).
% 1.56/0.56  fof(f19,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.56/0.56    inference(ennf_transformation,[],[f12])).
% 1.56/0.56  fof(f12,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.56/0.56  fof(f35,plain,(
% 1.56/0.56    r1_tarski(k2_relat_1(sK1),sK0)),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  fof(f66,plain,(
% 1.56/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.56    inference(equality_resolution,[],[f52])).
% 1.56/0.56  fof(f52,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.56    inference(cnf_transformation,[],[f3])).
% 1.56/0.56  fof(f3,axiom,(
% 1.56/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.56  fof(f33,plain,(
% 1.56/0.56    v1_relat_1(sK1)),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  fof(f102,plain,(
% 1.56/0.56    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl4_2),
% 1.56/0.56    inference(avatar_component_clause,[],[f100])).
% 1.56/0.56  fof(f100,plain,(
% 1.56/0.56    spl4_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.56/0.56  fof(f82,plain,(
% 1.56/0.56    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f75,f46])).
% 1.56/0.56  fof(f46,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f23])).
% 1.56/0.56  fof(f23,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.56    inference(ennf_transformation,[],[f11])).
% 1.56/0.56  fof(f11,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.56/0.56  fof(f306,plain,(
% 1.56/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl4_2 | ~spl4_6 | ~spl4_8)),
% 1.56/0.56    inference(backward_demodulation,[],[f269,f298])).
% 1.56/0.56  fof(f269,plain,(
% 1.56/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (spl4_2 | ~spl4_6 | ~spl4_8)),
% 1.56/0.56    inference(backward_demodulation,[],[f167,f259])).
% 1.56/0.56  fof(f167,plain,(
% 1.56/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) | spl4_2),
% 1.56/0.56    inference(backward_demodulation,[],[f75,f165])).
% 1.56/0.56  fof(f309,plain,(
% 1.56/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_6 | ~spl4_8)),
% 1.56/0.56    inference(backward_demodulation,[],[f273,f298])).
% 1.56/0.56  fof(f273,plain,(
% 1.56/0.56    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl4_2 | ~spl4_6 | ~spl4_8)),
% 1.56/0.56    inference(backward_demodulation,[],[f176,f259])).
% 1.56/0.56  fof(f176,plain,(
% 1.56/0.56    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl4_2),
% 1.56/0.56    inference(backward_demodulation,[],[f102,f165])).
% 1.56/0.56  fof(f240,plain,(
% 1.56/0.56    spl4_8),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f237])).
% 1.56/0.56  fof(f237,plain,(
% 1.56/0.56    $false | spl4_8),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f68,f66,f227,f60])).
% 1.56/0.56  fof(f60,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f31])).
% 1.56/0.56  fof(f31,plain,(
% 1.56/0.56    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.56/0.56    inference(flattening,[],[f30])).
% 1.56/0.56  fof(f30,plain,(
% 1.56/0.56    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.56/0.56    inference(ennf_transformation,[],[f5])).
% 1.56/0.56  fof(f5,axiom,(
% 1.56/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.56/0.56  fof(f227,plain,(
% 1.56/0.56    ~v1_xboole_0(k1_xboole_0) | spl4_8),
% 1.56/0.56    inference(avatar_component_clause,[],[f225])).
% 1.56/0.56  fof(f68,plain,(
% 1.56/0.56    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.56/0.56    inference(equality_resolution,[],[f59])).
% 1.56/0.56  fof(f59,plain,(
% 1.56/0.56    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f29])).
% 1.56/0.56  fof(f29,plain,(
% 1.56/0.56    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.56/0.56  fof(f232,plain,(
% 1.56/0.56    spl4_7),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f229])).
% 1.56/0.56  fof(f229,plain,(
% 1.56/0.56    $false | spl4_7),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f33,f223])).
% 1.56/0.56  fof(f223,plain,(
% 1.56/0.56    ~v1_relat_1(sK1) | spl4_7),
% 1.56/0.56    inference(avatar_component_clause,[],[f221])).
% 1.56/0.56  fof(f221,plain,(
% 1.56/0.56    spl4_7 <=> v1_relat_1(sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.56/0.56  fof(f228,plain,(
% 1.56/0.56    spl4_6 | ~spl4_7 | ~spl4_8 | spl4_2 | ~spl4_4),
% 1.56/0.56    inference(avatar_split_clause,[],[f209,f133,f100,f225,f221,f217])).
% 1.56/0.56  fof(f133,plain,(
% 1.56/0.56    spl4_4 <=> sK0 = k2_relat_1(sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.56/0.56  fof(f209,plain,(
% 1.56/0.56    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK1) | v1_xboole_0(sK1) | (spl4_2 | ~spl4_4)),
% 1.56/0.56    inference(superposition,[],[f54,f195])).
% 1.56/0.56  fof(f195,plain,(
% 1.56/0.56    k1_xboole_0 = k2_relat_1(sK1) | (spl4_2 | ~spl4_4)),
% 1.56/0.56    inference(forward_demodulation,[],[f135,f165])).
% 1.56/0.56  fof(f135,plain,(
% 1.56/0.56    sK0 = k2_relat_1(sK1) | ~spl4_4),
% 1.56/0.56    inference(avatar_component_clause,[],[f133])).
% 1.56/0.56  fof(f54,plain,(
% 1.56/0.56    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f27])).
% 1.56/0.56  fof(f27,plain,(
% 1.56/0.56    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.56/0.56    inference(flattening,[],[f26])).
% 1.56/0.56  fof(f26,plain,(
% 1.56/0.56    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,axiom,(
% 1.56/0.56    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 1.56/0.56  fof(f193,plain,(
% 1.56/0.56    spl4_2 | spl4_5),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f190])).
% 1.56/0.56  fof(f190,plain,(
% 1.56/0.56    $false | (spl4_2 | spl4_5)),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f68,f66,f181,f60])).
% 1.56/0.56  fof(f181,plain,(
% 1.56/0.56    ~v1_xboole_0(k1_xboole_0) | (spl4_2 | spl4_5)),
% 1.56/0.56    inference(backward_demodulation,[],[f145,f165])).
% 1.56/0.56  fof(f145,plain,(
% 1.56/0.56    ~v1_xboole_0(sK0) | spl4_5),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f141,f57])).
% 1.56/0.56  fof(f57,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f1])).
% 1.56/0.56  fof(f1,axiom,(
% 1.56/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.56/0.56  fof(f141,plain,(
% 1.56/0.56    r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0) | spl4_5),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f139,f49])).
% 1.56/0.56  fof(f49,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f25,plain,(
% 1.56/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f2])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.56  fof(f139,plain,(
% 1.56/0.56    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl4_5),
% 1.56/0.56    inference(avatar_component_clause,[],[f137])).
% 1.56/0.56  fof(f137,plain,(
% 1.56/0.56    spl4_5 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.56/0.56  fof(f140,plain,(
% 1.56/0.56    spl4_4 | ~spl4_5),
% 1.56/0.56    inference(avatar_split_clause,[],[f77,f137,f133])).
% 1.56/0.56  fof(f77,plain,(
% 1.56/0.56    ~r1_tarski(sK0,k2_relat_1(sK1)) | sK0 = k2_relat_1(sK1)),
% 1.56/0.56    inference(resolution,[],[f35,f53])).
% 1.56/0.56  fof(f53,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.56/0.56    inference(cnf_transformation,[],[f3])).
% 1.56/0.56  fof(f119,plain,(
% 1.56/0.56    spl4_1),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f114])).
% 1.56/0.56  fof(f114,plain,(
% 1.56/0.56    $false | spl4_1),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f83,f98,f38])).
% 1.56/0.56  fof(f38,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f7])).
% 1.56/0.56  fof(f7,axiom,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.56/0.56  fof(f98,plain,(
% 1.56/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl4_1),
% 1.56/0.56    inference(avatar_component_clause,[],[f96])).
% 1.56/0.56  fof(f96,plain,(
% 1.56/0.56    spl4_1 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.56/0.56  fof(f83,plain,(
% 1.56/0.56    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f75,f39])).
% 1.56/0.56  fof(f39,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f7])).
% 1.56/0.56  fof(f107,plain,(
% 1.56/0.56    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.56/0.56    inference(avatar_split_clause,[],[f32,f104,f100,f96])).
% 1.56/0.56  fof(f32,plain,(
% 1.56/0.56    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  % SZS output end Proof for theBenchmark
% 1.56/0.56  % (5065)------------------------------
% 1.56/0.56  % (5065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (5065)Termination reason: Refutation
% 1.56/0.56  
% 1.56/0.56  % (5065)Memory used [KB]: 6396
% 1.56/0.56  % (5065)Time elapsed: 0.132 s
% 1.56/0.56  % (5065)------------------------------
% 1.56/0.56  % (5065)------------------------------
% 1.56/0.57  % (5060)Success in time 0.197 s
%------------------------------------------------------------------------------
