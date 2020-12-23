%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 137 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  263 ( 420 expanded)
%              Number of equality atoms :   60 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2735)Refutation not found, incomplete strategy% (2735)------------------------------
% (2735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2735)Termination reason: Refutation not found, incomplete strategy

% (2735)Memory used [KB]: 6140
% (2735)Time elapsed: 0.077 s
% (2735)------------------------------
% (2735)------------------------------
fof(f273,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f106,f119,f146,f152,f269])).

fof(f269,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f267,f159])).

fof(f159,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f121,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f141,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f141,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_7
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f121,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f85,f105])).

fof(f105,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f85,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f267,plain,
    ( v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f263])).

fof(f263,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(superposition,[],[f189,f158])).

fof(f158,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f130,f155])).

fof(f130,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f100,f105])).

fof(f100,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_3
  <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f189,plain,
    ( ! [X9] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X9,sK0)
        | v1_funct_2(sK0,k1_xboole_0,X9) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f188,f40])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f188,plain,
    ( ! [X9] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X9,sK0)
        | v1_funct_2(sK0,k1_xboole_0,X9) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f174,f71])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f174,plain,
    ( ! [X9] :
        ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X9))
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X9,sK0)
        | v1_funct_2(sK0,k1_xboole_0,X9) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f135,f73])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f135,plain,
    ( ! [X0] :
        ( m1_subset_1(sK0,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f125,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f125,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f120,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f120,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f80,f105])).

fof(f80,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_1
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f152,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f149,f40])).

fof(f149,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_8 ),
    inference(resolution,[],[f145,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f145,plain,
    ( r2_hidden(sK3(sK0),k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_8
  <=> r2_hidden(sK3(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f146,plain,
    ( spl4_7
    | spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f138,f103,f143,f140])).

fof(f138,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f136,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_4 ),
    inference(superposition,[],[f52,f105])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

fof(f119,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f117,f80])).

fof(f117,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl4_3 ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl4_3 ),
    inference(superposition,[],[f101,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f97,f83,f79,f103,f99])).

fof(f97,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f91,f85])).

fof(f91,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f80,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f88,f38])).

fof(f88,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f87,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl4_1 ),
    inference(resolution,[],[f81,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f86,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f77,f83,f79])).

fof(f77,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f37,f39])).

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (2738)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (2736)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (2735)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (2750)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.51  % (2744)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.51  % (2749)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.51  % (2738)Refutation not found, incomplete strategy% (2738)------------------------------
% 0.19/0.51  % (2738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2738)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (2738)Memory used [KB]: 10618
% 0.19/0.51  % (2738)Time elapsed: 0.079 s
% 0.19/0.51  % (2738)------------------------------
% 0.19/0.51  % (2738)------------------------------
% 0.19/0.51  % (2736)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  % (2735)Refutation not found, incomplete strategy% (2735)------------------------------
% 0.19/0.51  % (2735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2735)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (2735)Memory used [KB]: 6140
% 0.19/0.51  % (2735)Time elapsed: 0.077 s
% 0.19/0.51  % (2735)------------------------------
% 0.19/0.51  % (2735)------------------------------
% 0.19/0.51  fof(f273,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f86,f90,f106,f119,f146,f152,f269])).
% 0.19/0.51  fof(f269,plain,(
% 0.19/0.51    ~spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f268])).
% 0.19/0.51  fof(f268,plain,(
% 0.19/0.51    $false | (~spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.19/0.51    inference(subsumption_resolution,[],[f267,f159])).
% 0.19/0.51  fof(f159,plain,(
% 0.19/0.51    ~v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_7)),
% 0.19/0.51    inference(backward_demodulation,[],[f121,f155])).
% 0.19/0.51  fof(f155,plain,(
% 0.19/0.51    k1_xboole_0 = k1_relat_1(sK0) | ~spl4_7),
% 0.19/0.51    inference(resolution,[],[f141,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.19/0.51    inference(ennf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,axiom,(
% 0.19/0.51    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.19/0.51  fof(f141,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0))) ) | ~spl4_7),
% 0.19/0.51    inference(avatar_component_clause,[],[f140])).
% 0.19/0.51  fof(f140,plain,(
% 0.19/0.51    spl4_7 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.51  fof(f121,plain,(
% 0.19/0.51    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 0.19/0.51    inference(backward_demodulation,[],[f85,f105])).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(sK0) | ~spl4_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f103])).
% 0.19/0.51  fof(f103,plain,(
% 0.19/0.51    spl4_4 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl4_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f83])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    spl4_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.51  fof(f267,plain,(
% 0.19/0.51    v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f263])).
% 0.19/0.51  fof(f263,plain,(
% 0.19/0.51    k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.19/0.51    inference(superposition,[],[f189,f158])).
% 0.19/0.51  fof(f158,plain,(
% 0.19/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.19/0.51    inference(backward_demodulation,[],[f130,f155])).
% 0.19/0.51  fof(f130,plain,(
% 0.19/0.51    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0) | (~spl4_3 | ~spl4_4)),
% 0.19/0.51    inference(forward_demodulation,[],[f100,f105])).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl4_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f99])).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    spl4_3 <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.51  fof(f189,plain,(
% 0.19/0.51    ( ! [X9] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X9,sK0) | v1_funct_2(sK0,k1_xboole_0,X9)) ) | (~spl4_1 | ~spl4_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f188,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    v1_xboole_0(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    v1_xboole_0(k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.51  fof(f188,plain,(
% 0.19/0.51    ( ! [X9] : (~v1_xboole_0(k1_xboole_0) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X9,sK0) | v1_funct_2(sK0,k1_xboole_0,X9)) ) | (~spl4_1 | ~spl4_4)),
% 0.19/0.51    inference(forward_demodulation,[],[f174,f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.51    inference(equality_resolution,[],[f57])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.51  fof(f174,plain,(
% 0.19/0.51    ( ! [X9] : (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X9)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X9,sK0) | v1_funct_2(sK0,k1_xboole_0,X9)) ) | (~spl4_1 | ~spl4_4)),
% 0.19/0.51    inference(resolution,[],[f135,f73])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.19/0.51    inference(equality_resolution,[],[f65])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(flattening,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.51  fof(f135,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(sK0,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | (~spl4_1 | ~spl4_4)),
% 0.19/0.51    inference(superposition,[],[f125,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.51  fof(f125,plain,(
% 0.19/0.51    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_1 | ~spl4_4)),
% 0.19/0.51    inference(forward_demodulation,[],[f120,f70])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f58])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f120,plain,(
% 0.19/0.51    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | (~spl4_1 | ~spl4_4)),
% 0.19/0.51    inference(backward_demodulation,[],[f80,f105])).
% 0.19/0.51  fof(f80,plain,(
% 0.19/0.51    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl4_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f79])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    spl4_1 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.51  fof(f152,plain,(
% 0.19/0.51    ~spl4_8),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f151])).
% 0.19/0.51  fof(f151,plain,(
% 0.19/0.51    $false | ~spl4_8),
% 0.19/0.51    inference(subsumption_resolution,[],[f149,f40])).
% 0.19/0.51  fof(f149,plain,(
% 0.19/0.51    ~v1_xboole_0(k1_xboole_0) | ~spl4_8),
% 0.19/0.51    inference(resolution,[],[f145,f48])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.51  fof(f145,plain,(
% 0.19/0.51    r2_hidden(sK3(sK0),k1_xboole_0) | ~spl4_8),
% 0.19/0.51    inference(avatar_component_clause,[],[f143])).
% 0.19/0.51  fof(f143,plain,(
% 0.19/0.51    spl4_8 <=> r2_hidden(sK3(sK0),k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.51  fof(f146,plain,(
% 0.19/0.51    spl4_7 | spl4_8 | ~spl4_4),
% 0.19/0.51    inference(avatar_split_clause,[],[f138,f103,f143,f140])).
% 0.19/0.51  fof(f138,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(sK3(sK0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK0))) ) | ~spl4_4),
% 0.19/0.51    inference(subsumption_resolution,[],[f136,f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    v1_relat_1(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,negated_conjecture,(
% 0.19/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.19/0.51    inference(negated_conjecture,[],[f19])).
% 0.19/0.51  fof(f19,conjecture,(
% 0.19/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.19/0.51  fof(f136,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(sK3(sK0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | ~spl4_4),
% 0.19/0.51    inference(superposition,[],[f52,f105])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).
% 0.19/0.51  fof(f119,plain,(
% 0.19/0.51    ~spl4_1 | spl4_3),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f118])).
% 0.19/0.51  fof(f118,plain,(
% 0.19/0.51    $false | (~spl4_1 | spl4_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f117,f80])).
% 0.19/0.51  fof(f117,plain,(
% 0.19/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl4_3),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f116])).
% 0.19/0.51  fof(f116,plain,(
% 0.19/0.51    k1_relat_1(sK0) != k1_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl4_3),
% 0.19/0.51    inference(superposition,[],[f101,f61])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.51  fof(f101,plain,(
% 0.19/0.51    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | spl4_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f99])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    ~spl4_3 | spl4_4 | ~spl4_1 | spl4_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f97,f83,f79,f103,f99])).
% 0.19/0.51  fof(f97,plain,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(sK0) | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | (~spl4_1 | spl4_2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f91,f85])).
% 0.19/0.51  fof(f91,plain,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(sK0) | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl4_1),
% 0.19/0.51    inference(resolution,[],[f80,f67])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f34])).
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    spl4_1),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f89])).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    $false | spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f88,f38])).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    ~v1_relat_1(sK0) | spl4_1),
% 0.19/0.51    inference(resolution,[],[f87,f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl4_1),
% 0.19/0.51    inference(resolution,[],[f81,f54])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl4_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f79])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    ~spl4_1 | ~spl4_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f77,f83,f79])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.19/0.51    inference(subsumption_resolution,[],[f37,f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    v1_funct_1(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ~v1_funct_1(sK0) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (2736)------------------------------
% 0.19/0.51  % (2736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2736)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (2736)Memory used [KB]: 10746
% 0.19/0.51  % (2736)Time elapsed: 0.080 s
% 0.19/0.51  % (2736)------------------------------
% 0.19/0.51  % (2736)------------------------------
% 0.19/0.52  % (2731)Success in time 0.157 s
%------------------------------------------------------------------------------
