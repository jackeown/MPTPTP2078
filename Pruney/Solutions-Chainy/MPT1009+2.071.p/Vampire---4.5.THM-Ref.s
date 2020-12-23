%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 135 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  275 ( 373 expanded)
%              Number of equality atoms :   78 (  89 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f86,f92,f100,f109,f123,f230,f330,f359])).

fof(f359,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_7
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_7
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f355,f103])).

fof(f103,plain,
    ( ! [X2] : r1_tarski(k9_relat_1(sK3,X2),k2_relat_1(sK3))
    | ~ spl4_6 ),
    inference(resolution,[],[f99,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f99,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f355,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_6
    | spl4_7
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f108,f353])).

fof(f353,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(equality_resolution,[],[f338])).

fof(f338,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f337,f99])).

fof(f337,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | ~ v1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f335,f70])).

fof(f70,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f335,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_19 ),
    inference(superposition,[],[f48,f329])).

fof(f329,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_19
  <=> k1_tarski(sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f108,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_7
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f330,plain,
    ( spl4_19
    | ~ spl4_4
    | ~ spl4_6
    | spl4_16 ),
    inference(avatar_split_clause,[],[f314,f179,f97,f83,f327])).

fof(f83,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f179,plain,
    ( spl4_16
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f314,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_6
    | spl4_16 ),
    inference(resolution,[],[f261,f85])).

fof(f85,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        | k1_tarski(X0) = k1_relat_1(sK3) )
    | ~ spl4_6
    | spl4_16 ),
    inference(subsumption_resolution,[],[f141,f180])).

fof(f180,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k1_relat_1(sK3)
        | k1_tarski(X0) = k1_relat_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) )
    | ~ spl4_6 ),
    inference(superposition,[],[f134,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( sK3 = k7_relat_1(sK3,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f101,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | sK3 = k7_relat_1(sK3,X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f99,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f134,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0)))
        | k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0))) )
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0)))
        | k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0)))
        | k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0))) )
    | ~ spl4_6 ),
    inference(superposition,[],[f104,f42])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f104,plain,
    ( ! [X0,X1] :
        ( k2_tarski(X0,X1) = k1_relat_1(k7_relat_1(sK3,k2_tarski(X0,X1)))
        | k1_tarski(X1) = k1_relat_1(k7_relat_1(sK3,k2_tarski(X0,X1)))
        | k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k2_tarski(X0,X1)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k2_tarski(X0,X1))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f102,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f102,plain,
    ( ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X1)
    | ~ spl4_6 ),
    inference(resolution,[],[f99,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f230,plain,
    ( ~ spl4_6
    | spl4_9
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl4_6
    | spl4_9
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f228,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f228,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(k1_funct_1(k1_xboole_0,sK0))))
    | ~ spl4_6
    | spl4_9
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f204,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f204,plain,
    ( ~ m1_subset_1(k9_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(k1_xboole_0,sK0))))
    | ~ spl4_6
    | spl4_9
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f122,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f190,f99])).

fof(f190,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | ~ spl4_16 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | ~ spl4_16 ),
    inference(superposition,[],[f43,f181])).

fof(f181,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f122,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0))))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_9
  <=> m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f123,plain,
    ( ~ spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f110,f106,f120])).

fof(f110,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0))))
    | spl4_7 ),
    inference(resolution,[],[f108,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f109,plain,
    ( ~ spl4_7
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f95,f89,f83,f106])).

fof(f89,plain,
    ( spl4_5
  <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f95,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f94,f85])).

fof(f94,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | spl4_5 ),
    inference(superposition,[],[f91,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f91,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f100,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f87,f83,f97])).

fof(f87,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f39,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f86,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:35:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (27951)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (27961)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.49  % (27951)Refutation not found, incomplete strategy% (27951)------------------------------
% 0.22/0.49  % (27951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27951)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (27951)Memory used [KB]: 10618
% 0.22/0.49  % (27951)Time elapsed: 0.072 s
% 0.22/0.49  % (27951)------------------------------
% 0.22/0.49  % (27951)------------------------------
% 0.22/0.51  % (27961)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f360,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f71,f86,f92,f100,f109,f123,f230,f330,f359])).
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    ~spl4_1 | ~spl4_6 | spl4_7 | ~spl4_19),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f358])).
% 0.22/0.51  fof(f358,plain,(
% 0.22/0.51    $false | (~spl4_1 | ~spl4_6 | spl4_7 | ~spl4_19)),
% 0.22/0.51    inference(subsumption_resolution,[],[f355,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X2] : (r1_tarski(k9_relat_1(sK3,X2),k2_relat_1(sK3))) ) | ~spl4_6),
% 0.22/0.51    inference(resolution,[],[f99,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl4_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl4_6 <=> v1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.51  fof(f355,plain,(
% 0.22/0.51    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (~spl4_1 | ~spl4_6 | spl4_7 | ~spl4_19)),
% 0.22/0.51    inference(backward_demodulation,[],[f108,f353])).
% 0.22/0.52  fof(f353,plain,(
% 0.22/0.52    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_1 | ~spl4_6 | ~spl4_19)),
% 0.22/0.52    inference(equality_resolution,[],[f338])).
% 0.22/0.52  fof(f338,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_6 | ~spl4_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f337,f99])).
% 0.22/0.52  fof(f337,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | ~v1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f335,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    v1_funct_1(sK3) | ~spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    spl4_1 <=> v1_funct_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f335,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | ~spl4_19),
% 0.22/0.52    inference(superposition,[],[f48,f329])).
% 0.22/0.52  fof(f329,plain,(
% 0.22/0.52    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f327])).
% 0.22/0.52  fof(f327,plain,(
% 0.22/0.52    spl4_19 <=> k1_tarski(sK0) = k1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    spl4_7 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.52  fof(f330,plain,(
% 0.22/0.52    spl4_19 | ~spl4_4 | ~spl4_6 | spl4_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f314,f179,f97,f83,f327])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    spl4_16 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    k1_tarski(sK0) = k1_relat_1(sK3) | (~spl4_4 | ~spl4_6 | spl4_16)),
% 0.22/0.52    inference(resolution,[],[f261,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl4_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f83])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | k1_tarski(X0) = k1_relat_1(sK3)) ) | (~spl4_6 | spl4_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f180])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    k1_xboole_0 != k1_relat_1(sK3) | spl4_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f179])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k1_relat_1(sK3) | k1_tarski(X0) = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))) ) | ~spl4_6),
% 0.22/0.52    inference(superposition,[],[f134,f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK3 = k7_relat_1(sK3,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_6),
% 0.22/0.52    inference(resolution,[],[f101,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) ) | ~spl4_6),
% 0.22/0.52    inference(resolution,[],[f99,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0))) | k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0)))) ) | ~spl4_6),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0))) | k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0))) | k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_tarski(X0)))) ) | ~spl4_6),
% 0.22/0.52    inference(superposition,[],[f104,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_relat_1(k7_relat_1(sK3,k2_tarski(X0,X1))) | k1_tarski(X1) = k1_relat_1(k7_relat_1(sK3,k2_tarski(X0,X1))) | k1_tarski(X0) = k1_relat_1(k7_relat_1(sK3,k2_tarski(X0,X1))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k2_tarski(X0,X1)))) ) | ~spl4_6),
% 0.22/0.52    inference(resolution,[],[f102,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X1)) ) | ~spl4_6),
% 0.22/0.52    inference(resolution,[],[f99,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    ~spl4_6 | spl4_9 | ~spl4_16),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f229])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    $false | (~spl4_6 | spl4_9 | ~spl4_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f228,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(k1_funct_1(k1_xboole_0,sK0)))) | (~spl4_6 | spl4_9 | ~spl4_16)),
% 0.22/0.52    inference(forward_demodulation,[],[f204,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    ~m1_subset_1(k9_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(k1_xboole_0,sK0)))) | (~spl4_6 | spl4_9 | ~spl4_16)),
% 0.22/0.52    inference(backward_demodulation,[],[f122,f191])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    k1_xboole_0 = sK3 | (~spl4_6 | ~spl4_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f99])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | k1_xboole_0 = sK3 | ~spl4_16),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f189])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK3) | k1_xboole_0 = sK3 | ~spl4_16),
% 0.22/0.52    inference(superposition,[],[f43,f181])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f179])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0)))) | spl4_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    spl4_9 <=> m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ~spl4_9 | spl4_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f110,f106,f120])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0)))) | spl4_7),
% 0.22/0.52    inference(resolution,[],[f108,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ~spl4_7 | ~spl4_4 | spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f95,f89,f83,f106])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl4_5 <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | (~spl4_4 | spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f94,f85])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | spl4_5),
% 0.22/0.52    inference(superposition,[],[f91,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f89])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    spl4_6 | ~spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f87,f83,f97])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    v1_relat_1(sK3) | ~spl4_4),
% 0.22/0.52    inference(resolution,[],[f85,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ~spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f39,f89])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f17])).
% 0.22/0.52  fof(f17,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f37,f83])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f35,f68])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (27961)------------------------------
% 0.22/0.52  % (27961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27961)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (27961)Memory used [KB]: 10874
% 0.22/0.52  % (27961)Time elapsed: 0.091 s
% 0.22/0.52  % (27961)------------------------------
% 0.22/0.52  % (27961)------------------------------
% 0.22/0.52  % (27940)Success in time 0.155 s
%------------------------------------------------------------------------------
