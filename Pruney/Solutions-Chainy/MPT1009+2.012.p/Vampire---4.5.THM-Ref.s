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
% DateTime   : Thu Dec  3 13:04:27 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 238 expanded)
%              Number of leaves         :   31 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  356 ( 573 expanded)
%              Number of equality atoms :   60 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f812,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f94,f106,f110,f116,f120,f130,f188,f227,f401,f479,f490,f516,f751,f754,f808])).

fof(f808,plain,
    ( ~ spl5_4
    | spl5_6
    | ~ spl5_35 ),
    inference(avatar_contradiction_clause,[],[f807])).

fof(f807,plain,
    ( $false
    | ~ spl5_4
    | spl5_6
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f802,f112])).

fof(f112,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f105,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f105,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f802,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl5_6
    | ~ spl5_35 ),
    inference(superposition,[],[f115,f400])).

fof(f400,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl5_35
  <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f115,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_6
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f754,plain,
    ( ~ spl5_4
    | ~ spl5_31
    | spl5_48 ),
    inference(avatar_contradiction_clause,[],[f753])).

fof(f753,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_31
    | spl5_48 ),
    inference(subsumption_resolution,[],[f752,f497])).

fof(f497,plain,(
    ! [X1] : r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f491,f475])).

fof(f475,plain,(
    ! [X4,X5] : k2_relat_1(k1_xboole_0) = k2_relset_1(X4,X5,k1_xboole_0) ),
    inference(resolution,[],[f60,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f491,plain,(
    ! [X0,X1] : r1_tarski(k2_relset_1(X0,X1,k1_xboole_0),X1) ),
    inference(resolution,[],[f473,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f473,plain,(
    ! [X2,X1] : m1_subset_1(k2_relset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f60,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f752,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl5_4
    | ~ spl5_31
    | spl5_48 ),
    inference(forward_demodulation,[],[f750,f566])).

fof(f566,plain,
    ( ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
    | ~ spl5_4
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f555,f497])).

fof(f555,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k9_relat_1(k1_xboole_0,X0))
        | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) )
    | ~ spl5_4
    | ~ spl5_31 ),
    inference(superposition,[],[f157,f380])).

fof(f380,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl5_31
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0))
        | k2_relat_1(sK3) = k9_relat_1(sK3,X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f112,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f750,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl5_48 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl5_48
  <=> r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f751,plain,
    ( ~ spl5_48
    | spl5_6
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f413,f379,f114,f749])).

fof(f413,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl5_6
    | ~ spl5_31 ),
    inference(superposition,[],[f115,f380])).

fof(f516,plain,
    ( spl5_31
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f511,f311,f379])).

fof(f311,plain,
    ( spl5_29
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f511,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f509,f472])).

fof(f472,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f60,f46])).

fof(f509,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3
    | ~ spl5_29 ),
    inference(resolution,[],[f312,f52])).

fof(f312,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f311])).

fof(f490,plain,
    ( spl5_29
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f338,f225,f311])).

fof(f225,plain,
    ( spl5_25
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f338,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_25 ),
    inference(resolution,[],[f226,f46])).

fof(f226,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f225])).

fof(f479,plain,(
    ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f285,f472])).

fof(f285,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,sK4(k1_xboole_0,X0,sK3))
    | ~ spl5_24 ),
    inference(resolution,[],[f223,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f223,plain,
    ( ! [X0] : r2_hidden(sK4(k1_xboole_0,X0,sK3),k1_xboole_0)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl5_24
  <=> ! [X0] : r2_hidden(sK4(k1_xboole_0,X0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f401,plain,
    ( spl5_35
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f329,f186,f92,f82,f399])).

fof(f82,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f92,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f186,plain,
    ( spl5_20
  <=> k1_tarski(sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f329,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(equality_resolution,[],[f238])).

fof(f238,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK0)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X1)) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(superposition,[],[f102,f187])).

fof(f187,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f186])).

fof(f102,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f85,f98])).

fof(f98,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_3 ),
    inference(resolution,[],[f93,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f93,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | k1_tarski(X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f83,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f83,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f227,plain,
    ( spl5_24
    | spl5_25
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f197,f183,f92,f82,f225,f222])).

fof(f183,plain,
    ( spl5_19
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f197,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
        | r2_hidden(sK4(k1_xboole_0,X0,sK3),k1_xboole_0) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f189,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f189,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_xboole_0,X0,sK3),k1_xboole_0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(superposition,[],[f101,f184])).

fof(f184,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f101,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(k1_relat_1(sK3),X1,sK3),k1_relat_1(sK3))
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f86,f98])).

fof(f86,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK3)
        | r2_hidden(sK4(k1_relat_1(sK3),X1,sK3),k1_relat_1(sK3))
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f83,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK4(X0,X1,X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f188,plain,
    ( spl5_19
    | spl5_20
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f134,f128,f186,f183])).

fof(f128,plain,
    ( spl5_9
  <=> r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f134,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_9 ),
    inference(resolution,[],[f129,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f129,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl5_9
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f122,f118,f104,f128])).

fof(f118,plain,
    ( spl5_7
  <=> v4_relat_1(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f122,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f121,f105])).

fof(f121,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f119,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f119,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f96,f92,f118])).

fof(f96,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f93,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f116,plain,
    ( ~ spl5_6
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f111,f108,f92,f114])).

fof(f108,plain,
    ( spl5_5
  <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f111,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl5_3
    | spl5_5 ),
    inference(forward_demodulation,[],[f109,f99])).

fof(f99,plain,
    ( ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl5_3 ),
    inference(resolution,[],[f93,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f109,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f44,f108])).

fof(f44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f106,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f98,f92,f104])).

fof(f94,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f42,f92])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:57:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.57  % (29207)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.57  % (29210)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.57  % (29200)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.57  % (29202)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.57  % (29187)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.58  % (29192)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.58  % (29190)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.58  % (29194)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.58  % (29200)Refutation not found, incomplete strategy% (29200)------------------------------
% 0.20/0.58  % (29200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (29183)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.59  % (29205)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.59  % (29200)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (29200)Memory used [KB]: 1791
% 0.20/0.59  % (29188)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.59  % (29200)Time elapsed: 0.152 s
% 0.20/0.59  % (29200)------------------------------
% 0.20/0.59  % (29200)------------------------------
% 0.20/0.59  % (29192)Refutation not found, incomplete strategy% (29192)------------------------------
% 0.20/0.59  % (29192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (29192)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (29192)Memory used [KB]: 10746
% 0.20/0.59  % (29192)Time elapsed: 0.161 s
% 0.20/0.59  % (29192)------------------------------
% 0.20/0.59  % (29192)------------------------------
% 0.20/0.59  % (29183)Refutation not found, incomplete strategy% (29183)------------------------------
% 0.20/0.59  % (29183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (29183)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (29183)Memory used [KB]: 1791
% 0.20/0.59  % (29183)Time elapsed: 0.125 s
% 0.20/0.59  % (29183)------------------------------
% 0.20/0.59  % (29183)------------------------------
% 0.20/0.59  % (29185)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.59  % (29184)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.59  % (29182)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.59  % (29189)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.59  % (29197)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.82/0.60  % (29210)Refutation not found, incomplete strategy% (29210)------------------------------
% 1.82/0.60  % (29210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (29210)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.60  
% 1.82/0.60  % (29210)Memory used [KB]: 10746
% 1.82/0.60  % (29210)Time elapsed: 0.169 s
% 1.82/0.60  % (29210)------------------------------
% 1.82/0.60  % (29210)------------------------------
% 1.82/0.60  % (29186)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.82/0.60  % (29196)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.82/0.61  % (29206)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.82/0.61  % (29199)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.82/0.61  % (29201)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.82/0.61  % (29203)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.82/0.61  % (29206)Refutation not found, incomplete strategy% (29206)------------------------------
% 1.82/0.61  % (29206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (29206)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  
% 1.82/0.61  % (29206)Memory used [KB]: 10746
% 1.82/0.61  % (29206)Time elapsed: 0.183 s
% 1.82/0.61  % (29206)------------------------------
% 1.82/0.61  % (29206)------------------------------
% 1.82/0.61  % (29199)Refutation not found, incomplete strategy% (29199)------------------------------
% 1.82/0.61  % (29199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (29199)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  
% 1.82/0.61  % (29199)Memory used [KB]: 1791
% 1.82/0.61  % (29199)Time elapsed: 0.183 s
% 1.82/0.61  % (29199)------------------------------
% 1.82/0.61  % (29199)------------------------------
% 1.82/0.61  % (29208)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.82/0.61  % (29195)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.82/0.61  % (29198)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.82/0.62  % (29209)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.95/0.62  % (29193)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.95/0.62  % (29198)Refutation not found, incomplete strategy% (29198)------------------------------
% 1.95/0.62  % (29198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.62  % (29204)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.95/0.62  % (29211)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.95/0.62  % (29191)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.95/0.62  % (29209)Refutation not found, incomplete strategy% (29209)------------------------------
% 1.95/0.62  % (29209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.62  % (29211)Refutation not found, incomplete strategy% (29211)------------------------------
% 1.95/0.62  % (29211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.62  % (29196)Refutation not found, incomplete strategy% (29196)------------------------------
% 1.95/0.62  % (29196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.63  % (29196)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.63  
% 1.95/0.63  % (29196)Memory used [KB]: 1791
% 1.95/0.63  % (29196)Time elapsed: 0.185 s
% 1.95/0.63  % (29196)------------------------------
% 1.95/0.63  % (29196)------------------------------
% 1.95/0.63  % (29211)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.63  
% 1.95/0.63  % (29211)Memory used [KB]: 1663
% 1.95/0.63  % (29211)Time elapsed: 0.200 s
% 1.95/0.64  % (29211)------------------------------
% 1.95/0.64  % (29211)------------------------------
% 1.95/0.64  % (29198)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.64  
% 1.95/0.64  % (29198)Memory used [KB]: 10618
% 1.95/0.64  % (29198)Time elapsed: 0.192 s
% 1.95/0.64  % (29198)------------------------------
% 1.95/0.64  % (29198)------------------------------
% 1.95/0.64  % (29209)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.64  
% 1.95/0.64  % (29209)Memory used [KB]: 6268
% 1.95/0.64  % (29209)Time elapsed: 0.190 s
% 1.95/0.64  % (29209)------------------------------
% 1.95/0.64  % (29209)------------------------------
% 2.20/0.65  % (29208)Refutation found. Thanks to Tanya!
% 2.20/0.65  % SZS status Theorem for theBenchmark
% 2.20/0.66  % SZS output start Proof for theBenchmark
% 2.20/0.66  fof(f812,plain,(
% 2.20/0.66    $false),
% 2.20/0.66    inference(avatar_sat_refutation,[],[f84,f94,f106,f110,f116,f120,f130,f188,f227,f401,f479,f490,f516,f751,f754,f808])).
% 2.20/0.66  fof(f808,plain,(
% 2.20/0.66    ~spl5_4 | spl5_6 | ~spl5_35),
% 2.20/0.66    inference(avatar_contradiction_clause,[],[f807])).
% 2.20/0.66  fof(f807,plain,(
% 2.20/0.66    $false | (~spl5_4 | spl5_6 | ~spl5_35)),
% 2.20/0.66    inference(subsumption_resolution,[],[f802,f112])).
% 2.20/0.66  fof(f112,plain,(
% 2.20/0.66    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl5_4),
% 2.20/0.66    inference(resolution,[],[f105,f68])).
% 2.20/0.66  fof(f68,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f38])).
% 2.20/0.66  fof(f38,plain,(
% 2.20/0.66    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.20/0.66    inference(ennf_transformation,[],[f11])).
% 2.20/0.66  fof(f11,axiom,(
% 2.20/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 2.20/0.66  fof(f105,plain,(
% 2.20/0.66    v1_relat_1(sK3) | ~spl5_4),
% 2.20/0.66    inference(avatar_component_clause,[],[f104])).
% 2.20/0.66  fof(f104,plain,(
% 2.20/0.66    spl5_4 <=> v1_relat_1(sK3)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.20/0.66  fof(f802,plain,(
% 2.20/0.66    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (spl5_6 | ~spl5_35)),
% 2.20/0.66    inference(superposition,[],[f115,f400])).
% 2.20/0.66  fof(f400,plain,(
% 2.20/0.66    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl5_35),
% 2.20/0.66    inference(avatar_component_clause,[],[f399])).
% 2.20/0.66  fof(f399,plain,(
% 2.20/0.66    spl5_35 <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 2.20/0.66  fof(f115,plain,(
% 2.20/0.66    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl5_6),
% 2.20/0.66    inference(avatar_component_clause,[],[f114])).
% 2.20/0.66  fof(f114,plain,(
% 2.20/0.66    spl5_6 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.20/0.66  fof(f754,plain,(
% 2.20/0.66    ~spl5_4 | ~spl5_31 | spl5_48),
% 2.20/0.66    inference(avatar_contradiction_clause,[],[f753])).
% 2.20/0.66  fof(f753,plain,(
% 2.20/0.66    $false | (~spl5_4 | ~spl5_31 | spl5_48)),
% 2.20/0.66    inference(subsumption_resolution,[],[f752,f497])).
% 2.20/0.66  fof(f497,plain,(
% 2.20/0.66    ( ! [X1] : (r1_tarski(k2_relat_1(k1_xboole_0),X1)) )),
% 2.20/0.66    inference(forward_demodulation,[],[f491,f475])).
% 2.20/0.66  fof(f475,plain,(
% 2.20/0.66    ( ! [X4,X5] : (k2_relat_1(k1_xboole_0) = k2_relset_1(X4,X5,k1_xboole_0)) )),
% 2.20/0.66    inference(resolution,[],[f60,f67])).
% 2.20/0.66  fof(f67,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f37])).
% 2.20/0.66  fof(f37,plain,(
% 2.20/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.66    inference(ennf_transformation,[],[f17])).
% 2.20/0.66  fof(f17,axiom,(
% 2.20/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.20/0.66  fof(f60,plain,(
% 2.20/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f7])).
% 2.20/0.66  fof(f7,axiom,(
% 2.20/0.66    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.20/0.66  fof(f491,plain,(
% 2.20/0.66    ( ! [X0,X1] : (r1_tarski(k2_relset_1(X0,X1,k1_xboole_0),X1)) )),
% 2.20/0.66    inference(resolution,[],[f473,f46])).
% 2.20/0.66  fof(f46,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f8])).
% 2.20/0.66  fof(f8,axiom,(
% 2.20/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.20/0.66  fof(f473,plain,(
% 2.20/0.66    ( ! [X2,X1] : (m1_subset_1(k2_relset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X2))) )),
% 2.20/0.66    inference(resolution,[],[f60,f71])).
% 2.20/0.66  fof(f71,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f40])).
% 2.20/0.66  fof(f40,plain,(
% 2.20/0.66    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.66    inference(ennf_transformation,[],[f16])).
% 2.20/0.66  fof(f16,axiom,(
% 2.20/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 2.20/0.66  fof(f752,plain,(
% 2.20/0.66    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (~spl5_4 | ~spl5_31 | spl5_48)),
% 2.20/0.66    inference(forward_demodulation,[],[f750,f566])).
% 2.20/0.66  fof(f566,plain,(
% 2.20/0.66    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl5_4 | ~spl5_31)),
% 2.20/0.66    inference(subsumption_resolution,[],[f555,f497])).
% 2.20/0.66  fof(f555,plain,(
% 2.20/0.66    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_xboole_0),k9_relat_1(k1_xboole_0,X0)) | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl5_4 | ~spl5_31)),
% 2.20/0.66    inference(superposition,[],[f157,f380])).
% 2.20/0.66  fof(f380,plain,(
% 2.20/0.66    k1_xboole_0 = sK3 | ~spl5_31),
% 2.20/0.66    inference(avatar_component_clause,[],[f379])).
% 2.20/0.66  fof(f379,plain,(
% 2.20/0.66    spl5_31 <=> k1_xboole_0 = sK3),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.20/0.66  fof(f157,plain,(
% 2.20/0.66    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0)) | k2_relat_1(sK3) = k9_relat_1(sK3,X0)) ) | ~spl5_4),
% 2.20/0.66    inference(resolution,[],[f112,f52])).
% 2.20/0.66  fof(f52,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.20/0.66    inference(cnf_transformation,[],[f1])).
% 2.20/0.66  fof(f1,axiom,(
% 2.20/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.20/0.66  fof(f750,plain,(
% 2.20/0.66    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl5_48),
% 2.20/0.66    inference(avatar_component_clause,[],[f749])).
% 2.20/0.66  fof(f749,plain,(
% 2.20/0.66    spl5_48 <=> r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 2.20/0.66  fof(f751,plain,(
% 2.20/0.66    ~spl5_48 | spl5_6 | ~spl5_31),
% 2.20/0.66    inference(avatar_split_clause,[],[f413,f379,f114,f749])).
% 2.20/0.66  fof(f413,plain,(
% 2.20/0.66    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (spl5_6 | ~spl5_31)),
% 2.20/0.66    inference(superposition,[],[f115,f380])).
% 2.20/0.66  fof(f516,plain,(
% 2.20/0.66    spl5_31 | ~spl5_29),
% 2.20/0.66    inference(avatar_split_clause,[],[f511,f311,f379])).
% 2.20/0.66  fof(f311,plain,(
% 2.20/0.66    spl5_29 <=> r1_tarski(sK3,k1_xboole_0)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.20/0.66  fof(f511,plain,(
% 2.20/0.66    k1_xboole_0 = sK3 | ~spl5_29),
% 2.20/0.66    inference(subsumption_resolution,[],[f509,f472])).
% 2.20/0.66  fof(f472,plain,(
% 2.20/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.20/0.66    inference(resolution,[],[f60,f46])).
% 2.20/0.66  fof(f509,plain,(
% 2.20/0.66    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3 | ~spl5_29),
% 2.20/0.66    inference(resolution,[],[f312,f52])).
% 2.20/0.66  fof(f312,plain,(
% 2.20/0.66    r1_tarski(sK3,k1_xboole_0) | ~spl5_29),
% 2.20/0.66    inference(avatar_component_clause,[],[f311])).
% 2.20/0.66  fof(f490,plain,(
% 2.20/0.66    spl5_29 | ~spl5_25),
% 2.20/0.66    inference(avatar_split_clause,[],[f338,f225,f311])).
% 2.20/0.66  fof(f225,plain,(
% 2.20/0.66    spl5_25 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.20/0.66  fof(f338,plain,(
% 2.20/0.66    r1_tarski(sK3,k1_xboole_0) | ~spl5_25),
% 2.20/0.66    inference(resolution,[],[f226,f46])).
% 2.20/0.66  fof(f226,plain,(
% 2.20/0.66    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl5_25),
% 2.20/0.66    inference(avatar_component_clause,[],[f225])).
% 2.20/0.66  fof(f479,plain,(
% 2.20/0.66    ~spl5_24),
% 2.20/0.66    inference(avatar_contradiction_clause,[],[f478])).
% 2.20/0.66  fof(f478,plain,(
% 2.20/0.66    $false | ~spl5_24),
% 2.20/0.66    inference(subsumption_resolution,[],[f285,f472])).
% 2.20/0.66  fof(f285,plain,(
% 2.20/0.66    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK4(k1_xboole_0,X0,sK3))) ) | ~spl5_24),
% 2.20/0.66    inference(resolution,[],[f223,f64])).
% 2.20/0.66  fof(f64,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f35])).
% 2.20/0.66  fof(f35,plain,(
% 2.20/0.66    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.20/0.66    inference(ennf_transformation,[],[f13])).
% 2.20/0.66  fof(f13,axiom,(
% 2.20/0.66    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.20/0.66  fof(f223,plain,(
% 2.20/0.66    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,X0,sK3),k1_xboole_0)) ) | ~spl5_24),
% 2.20/0.66    inference(avatar_component_clause,[],[f222])).
% 2.20/0.66  fof(f222,plain,(
% 2.20/0.66    spl5_24 <=> ! [X0] : r2_hidden(sK4(k1_xboole_0,X0,sK3),k1_xboole_0)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 2.20/0.66  fof(f401,plain,(
% 2.20/0.66    spl5_35 | ~spl5_1 | ~spl5_3 | ~spl5_20),
% 2.20/0.66    inference(avatar_split_clause,[],[f329,f186,f92,f82,f399])).
% 2.20/0.66  fof(f82,plain,(
% 2.20/0.66    spl5_1 <=> v1_funct_1(sK3)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.20/0.66  fof(f92,plain,(
% 2.20/0.66    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.20/0.66  fof(f186,plain,(
% 2.20/0.66    spl5_20 <=> k1_tarski(sK0) = k1_relat_1(sK3)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.20/0.66  fof(f329,plain,(
% 2.20/0.66    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl5_1 | ~spl5_3 | ~spl5_20)),
% 2.20/0.66    inference(equality_resolution,[],[f238])).
% 2.20/0.66  fof(f238,plain,(
% 2.20/0.66    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X1))) ) | (~spl5_1 | ~spl5_3 | ~spl5_20)),
% 2.20/0.66    inference(superposition,[],[f102,f187])).
% 2.20/0.66  fof(f187,plain,(
% 2.20/0.66    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl5_20),
% 2.20/0.66    inference(avatar_component_clause,[],[f186])).
% 2.20/0.66  fof(f102,plain,(
% 2.20/0.66    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl5_1 | ~spl5_3)),
% 2.20/0.66    inference(subsumption_resolution,[],[f85,f98])).
% 2.20/0.66  fof(f98,plain,(
% 2.20/0.66    v1_relat_1(sK3) | ~spl5_3),
% 2.20/0.66    inference(resolution,[],[f93,f61])).
% 2.20/0.66  fof(f61,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f32,plain,(
% 2.20/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.66    inference(ennf_transformation,[],[f14])).
% 2.20/0.66  fof(f14,axiom,(
% 2.20/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.20/0.66  fof(f93,plain,(
% 2.20/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl5_3),
% 2.20/0.66    inference(avatar_component_clause,[],[f92])).
% 2.20/0.66  fof(f85,plain,(
% 2.20/0.66    ( ! [X0] : (~v1_relat_1(sK3) | k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | ~spl5_1),
% 2.20/0.66    inference(resolution,[],[f83,f55])).
% 2.20/0.66  fof(f55,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f30])).
% 2.20/0.66  fof(f30,plain,(
% 2.20/0.66    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.20/0.66    inference(flattening,[],[f29])).
% 2.20/0.66  fof(f29,plain,(
% 2.20/0.66    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.20/0.66    inference(ennf_transformation,[],[f12])).
% 2.20/0.66  fof(f12,axiom,(
% 2.20/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 2.20/0.66  fof(f83,plain,(
% 2.20/0.66    v1_funct_1(sK3) | ~spl5_1),
% 2.20/0.66    inference(avatar_component_clause,[],[f82])).
% 2.20/0.66  fof(f227,plain,(
% 2.20/0.66    spl5_24 | spl5_25 | ~spl5_1 | ~spl5_3 | ~spl5_19),
% 2.20/0.66    inference(avatar_split_clause,[],[f197,f183,f92,f82,f225,f222])).
% 2.20/0.66  fof(f183,plain,(
% 2.20/0.66    spl5_19 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.20/0.66  fof(f197,plain,(
% 2.20/0.66    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(sK4(k1_xboole_0,X0,sK3),k1_xboole_0)) ) | (~spl5_1 | ~spl5_3 | ~spl5_19)),
% 2.20/0.66    inference(forward_demodulation,[],[f189,f80])).
% 2.20/0.66  fof(f80,plain,(
% 2.20/0.66    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.20/0.66    inference(equality_resolution,[],[f58])).
% 2.20/0.66  fof(f58,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f6])).
% 2.20/0.66  fof(f6,axiom,(
% 2.20/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.20/0.66  fof(f189,plain,(
% 2.20/0.66    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,X0,sK3),k1_xboole_0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_1 | ~spl5_3 | ~spl5_19)),
% 2.20/0.66    inference(superposition,[],[f101,f184])).
% 2.20/0.66  fof(f184,plain,(
% 2.20/0.66    k1_xboole_0 = k1_relat_1(sK3) | ~spl5_19),
% 2.20/0.66    inference(avatar_component_clause,[],[f183])).
% 2.20/0.66  fof(f101,plain,(
% 2.20/0.66    ( ! [X1] : (r2_hidden(sK4(k1_relat_1(sK3),X1,sK3),k1_relat_1(sK3)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))) ) | (~spl5_1 | ~spl5_3)),
% 2.20/0.66    inference(subsumption_resolution,[],[f86,f98])).
% 2.20/0.66  fof(f86,plain,(
% 2.20/0.66    ( ! [X1] : (~v1_relat_1(sK3) | r2_hidden(sK4(k1_relat_1(sK3),X1,sK3),k1_relat_1(sK3)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))) ) | ~spl5_1),
% 2.20/0.66    inference(resolution,[],[f83,f78])).
% 2.20/0.66  fof(f78,plain,(
% 2.20/0.66    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 2.20/0.66    inference(equality_resolution,[],[f53])).
% 2.20/0.66  fof(f53,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK4(X0,X1,X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f28])).
% 2.20/0.66  fof(f28,plain,(
% 2.20/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.20/0.66    inference(flattening,[],[f27])).
% 2.20/0.66  fof(f27,plain,(
% 2.20/0.66    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.20/0.66    inference(ennf_transformation,[],[f23])).
% 2.20/0.66  fof(f23,plain,(
% 2.20/0.66    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))))),
% 2.20/0.66    inference(pure_predicate_removal,[],[f19])).
% 2.20/0.66  fof(f19,axiom,(
% 2.20/0.66    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 2.20/0.66  fof(f188,plain,(
% 2.20/0.66    spl5_19 | spl5_20 | ~spl5_9),
% 2.20/0.66    inference(avatar_split_clause,[],[f134,f128,f186,f183])).
% 2.20/0.66  fof(f128,plain,(
% 2.20/0.66    spl5_9 <=> r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.20/0.66  fof(f134,plain,(
% 2.20/0.66    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~spl5_9),
% 2.20/0.66    inference(resolution,[],[f129,f47])).
% 2.20/0.66  fof(f47,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 2.20/0.66    inference(cnf_transformation,[],[f5])).
% 2.20/0.66  fof(f5,axiom,(
% 2.20/0.66    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.20/0.66  fof(f129,plain,(
% 2.20/0.66    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~spl5_9),
% 2.20/0.66    inference(avatar_component_clause,[],[f128])).
% 2.20/0.66  fof(f130,plain,(
% 2.20/0.66    spl5_9 | ~spl5_4 | ~spl5_7),
% 2.20/0.66    inference(avatar_split_clause,[],[f122,f118,f104,f128])).
% 2.20/0.66  fof(f118,plain,(
% 2.20/0.66    spl5_7 <=> v4_relat_1(sK3,k1_tarski(sK0))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.20/0.66  fof(f122,plain,(
% 2.20/0.66    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | (~spl5_4 | ~spl5_7)),
% 2.20/0.66    inference(subsumption_resolution,[],[f121,f105])).
% 2.20/0.66  fof(f121,plain,(
% 2.20/0.66    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3) | ~spl5_7),
% 2.20/0.66    inference(resolution,[],[f119,f66])).
% 2.20/0.66  fof(f66,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f36])).
% 2.20/0.66  fof(f36,plain,(
% 2.20/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.20/0.66    inference(ennf_transformation,[],[f10])).
% 2.20/0.66  fof(f10,axiom,(
% 2.20/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.20/0.66  fof(f119,plain,(
% 2.20/0.66    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl5_7),
% 2.20/0.66    inference(avatar_component_clause,[],[f118])).
% 2.20/0.66  fof(f120,plain,(
% 2.20/0.66    spl5_7 | ~spl5_3),
% 2.20/0.66    inference(avatar_split_clause,[],[f96,f92,f118])).
% 2.20/0.66  fof(f96,plain,(
% 2.20/0.66    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl5_3),
% 2.20/0.66    inference(resolution,[],[f93,f70])).
% 2.20/0.66  fof(f70,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f39])).
% 2.20/0.66  fof(f39,plain,(
% 2.20/0.66    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.66    inference(ennf_transformation,[],[f24])).
% 2.20/0.66  fof(f24,plain,(
% 2.20/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.20/0.66    inference(pure_predicate_removal,[],[f15])).
% 2.20/0.66  fof(f15,axiom,(
% 2.20/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.20/0.66  fof(f116,plain,(
% 2.20/0.66    ~spl5_6 | ~spl5_3 | spl5_5),
% 2.20/0.66    inference(avatar_split_clause,[],[f111,f108,f92,f114])).
% 2.20/0.66  fof(f108,plain,(
% 2.20/0.66    spl5_5 <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.20/0.66  fof(f111,plain,(
% 2.20/0.66    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | (~spl5_3 | spl5_5)),
% 2.20/0.66    inference(forward_demodulation,[],[f109,f99])).
% 2.20/0.66  fof(f99,plain,(
% 2.20/0.66    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl5_3),
% 2.20/0.66    inference(resolution,[],[f93,f56])).
% 2.20/0.66  fof(f56,plain,(
% 2.20/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f31])).
% 2.20/0.66  fof(f31,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.66    inference(ennf_transformation,[],[f18])).
% 2.20/0.66  fof(f18,axiom,(
% 2.20/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.20/0.66  fof(f109,plain,(
% 2.20/0.66    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl5_5),
% 2.20/0.66    inference(avatar_component_clause,[],[f108])).
% 2.20/0.66  fof(f110,plain,(
% 2.20/0.66    ~spl5_5),
% 2.20/0.66    inference(avatar_split_clause,[],[f44,f108])).
% 2.20/0.66  fof(f44,plain,(
% 2.20/0.66    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.20/0.66    inference(cnf_transformation,[],[f26])).
% 2.20/0.66  fof(f26,plain,(
% 2.20/0.66    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.20/0.66    inference(flattening,[],[f25])).
% 2.20/0.66  fof(f25,plain,(
% 2.20/0.66    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.20/0.66    inference(ennf_transformation,[],[f22])).
% 2.20/0.66  fof(f22,plain,(
% 2.20/0.66    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.20/0.66    inference(pure_predicate_removal,[],[f21])).
% 2.20/0.66  fof(f21,negated_conjecture,(
% 2.20/0.66    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.20/0.66    inference(negated_conjecture,[],[f20])).
% 2.20/0.66  fof(f20,conjecture,(
% 2.20/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 2.20/0.66  fof(f106,plain,(
% 2.20/0.66    spl5_4 | ~spl5_3),
% 2.20/0.66    inference(avatar_split_clause,[],[f98,f92,f104])).
% 2.20/0.66  fof(f94,plain,(
% 2.20/0.66    spl5_3),
% 2.20/0.66    inference(avatar_split_clause,[],[f42,f92])).
% 2.20/0.66  fof(f42,plain,(
% 2.20/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.20/0.66    inference(cnf_transformation,[],[f26])).
% 2.20/0.66  fof(f84,plain,(
% 2.20/0.66    spl5_1),
% 2.20/0.66    inference(avatar_split_clause,[],[f41,f82])).
% 2.20/0.66  fof(f41,plain,(
% 2.20/0.66    v1_funct_1(sK3)),
% 2.20/0.66    inference(cnf_transformation,[],[f26])).
% 2.20/0.66  % SZS output end Proof for theBenchmark
% 2.20/0.66  % (29208)------------------------------
% 2.20/0.66  % (29208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (29208)Termination reason: Refutation
% 2.20/0.66  
% 2.20/0.66  % (29208)Memory used [KB]: 6652
% 2.20/0.66  % (29208)Time elapsed: 0.236 s
% 2.20/0.66  % (29208)------------------------------
% 2.20/0.66  % (29208)------------------------------
% 2.20/0.67  % (29181)Success in time 0.297 s
%------------------------------------------------------------------------------
