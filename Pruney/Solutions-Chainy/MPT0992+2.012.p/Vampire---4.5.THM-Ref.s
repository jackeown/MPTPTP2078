%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 805 expanded)
%              Number of leaves         :   27 ( 207 expanded)
%              Depth                    :   17
%              Number of atoms          :  473 (5011 expanded)
%              Number of equality atoms :   86 (1064 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f120,f168,f255,f257,f768,f773,f840,f884,f938,f940,f941,f1006])).

fof(f1006,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f1005])).

fof(f1005,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f1004,f977])).

fof(f977,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f976,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f976,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f417,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f417,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK1)
    | spl4_2
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f298,f409])).

fof(f409,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(sK3,X0)
    | ~ spl4_16 ),
    inference(resolution,[],[f295,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f295,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl4_16
  <=> ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f298,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1)
    | spl4_2
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f179,f129])).

fof(f129,plain,
    ( sK0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f179,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f106,f150])).

fof(f150,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f136,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f136,plain,(
    ! [X0] :
      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f54,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1004,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f981,f945])).

fof(f945,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_9 ),
    inference(resolution,[],[f146,f63])).

fof(f146,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_9
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f981,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f946,f119])).

fof(f946,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f53,f114])).

fof(f53,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f941,plain,
    ( spl4_15
    | spl4_4 ),
    inference(avatar_split_clause,[],[f270,f113,f233])).

fof(f233,plain,
    ( spl4_15
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f270,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f266,f53])).

fof(f266,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f54,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f940,plain,
    ( ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f397,f144,f140])).

fof(f140,plain,
    ( spl4_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f397,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f54,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f938,plain,
    ( ~ spl4_8
    | spl4_16 ),
    inference(avatar_split_clause,[],[f489,f294,f140])).

fof(f489,plain,(
    ! [X0] :
      ( v1_xboole_0(k7_relat_1(sK3,X0))
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f182,f68])).

fof(f182,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f181,f52])).

fof(f181,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f180,f54])).

fof(f180,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f89,f150])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f884,plain,
    ( spl4_3
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f883])).

fof(f883,plain,
    ( $false
    | spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f872,f202])).

fof(f202,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f201,f187])).

fof(f187,plain,(
    ! [X1] : v1_relat_1(k7_relat_1(sK3,X1)) ),
    inference(resolution,[],[f182,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f201,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f189,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f189,plain,(
    ! [X3] : v5_relat_1(k7_relat_1(sK3,X3),sK1) ),
    inference(resolution,[],[f182,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f872,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_3
    | ~ spl4_15 ),
    inference(resolution,[],[f780,f841])).

fof(f841,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(forward_demodulation,[],[f110,f150])).

fof(f110,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f780,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f779,f187])).

fof(f779,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f775,f178])).

fof(f178,plain,(
    ! [X1] : v1_funct_1(k7_relat_1(sK3,X1)) ),
    inference(backward_demodulation,[],[f151,f150])).

fof(f151,plain,(
    ! [X1] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) ),
    inference(subsumption_resolution,[],[f137,f52])).

fof(f137,plain,(
    ! [X1] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f54,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f775,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_15 ),
    inference(superposition,[],[f71,f771])).

fof(f771,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_15 ),
    inference(resolution,[],[f55,f440])).

fof(f440,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f435,f132])).

fof(f132,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f78])).

fof(f435,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | ~ spl4_15 ),
    inference(superposition,[],[f65,f432])).

fof(f432,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f133,f235])).

fof(f235,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f233])).

fof(f133,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f54,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f55,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f840,plain,
    ( spl4_2
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f839])).

fof(f839,plain,
    ( $false
    | spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f838,f179])).

fof(f838,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_15 ),
    inference(resolution,[],[f778,f202])).

fof(f778,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f777,f187])).

fof(f777,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f774,f178])).

fof(f774,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_15 ),
    inference(superposition,[],[f70,f771])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f773,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f772,f127,f123])).

fof(f123,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f772,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f768,plain,
    ( spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f766,f182])).

fof(f766,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f765,f150])).

fof(f765,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f110,f129])).

fof(f257,plain,
    ( ~ spl4_5
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl4_5
    | spl4_8 ),
    inference(subsumption_resolution,[],[f253,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f253,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | spl4_8 ),
    inference(backward_demodulation,[],[f142,f119])).

fof(f142,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f255,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f252,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f252,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f125,f119])).

fof(f125,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f168,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f151,f102])).

fof(f102,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f120,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f56,f117,f113])).

fof(f56,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f57,f108,f104,f100])).

fof(f57,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (14824)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (14843)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.48  % (14835)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.48  % (14831)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (14821)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (14837)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (14822)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (14842)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (14829)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (14819)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (14841)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (14818)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (14840)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (14832)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (14834)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (14827)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (14823)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (14820)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (14833)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (14830)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.54  % (14826)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.55  % (14828)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.55  % (14819)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f1007,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f111,f120,f168,f255,f257,f768,f773,f840,f884,f938,f940,f941,f1006])).
% 0.20/0.55  fof(f1006,plain,(
% 0.20/0.55    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_16),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f1005])).
% 0.20/0.55  fof(f1005,plain,(
% 0.20/0.55    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_16)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1004,f977])).
% 0.20/0.55  fof(f977,plain,(
% 0.20/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_16)),
% 0.20/0.55    inference(forward_demodulation,[],[f976,f119])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl4_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f117])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    spl4_5 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.55  fof(f976,plain,(
% 0.20/0.55    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_7 | ~spl4_16)),
% 0.20/0.55    inference(forward_demodulation,[],[f417,f114])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl4_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f113])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    spl4_4 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.55  fof(f417,plain,(
% 0.20/0.55    ~v1_funct_2(k1_xboole_0,sK0,sK1) | (spl4_2 | ~spl4_7 | ~spl4_16)),
% 0.20/0.55    inference(forward_demodulation,[],[f298,f409])).
% 0.20/0.55  fof(f409,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl4_16),
% 0.20/0.55    inference(resolution,[],[f295,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.55  fof(f295,plain,(
% 0.20/0.55    ( ! [X0] : (v1_xboole_0(k7_relat_1(sK3,X0))) ) | ~spl4_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f294])).
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    spl4_16 <=> ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.55  fof(f298,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1) | (spl4_2 | ~spl4_7)),
% 0.20/0.55    inference(backward_demodulation,[],[f179,f129])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    sK0 = sK2 | ~spl4_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f127])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    spl4_7 <=> sK0 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.55  fof(f179,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.55    inference(backward_demodulation,[],[f106,f150])).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f136,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.55    inference(negated_conjecture,[],[f20])).
% 0.20/0.55  fof(f20,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) | ~v1_funct_1(sK3)) )),
% 0.20/0.55    inference(resolution,[],[f54,f87])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.55  fof(f1004,plain,(
% 0.20/0.55    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5 | ~spl4_9)),
% 0.20/0.55    inference(forward_demodulation,[],[f981,f945])).
% 0.20/0.55  fof(f945,plain,(
% 0.20/0.55    k1_xboole_0 = sK3 | ~spl4_9),
% 0.20/0.55    inference(resolution,[],[f146,f63])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    v1_xboole_0(sK3) | ~spl4_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f144])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    spl4_9 <=> v1_xboole_0(sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.55  fof(f981,plain,(
% 0.20/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.20/0.55    inference(forward_demodulation,[],[f946,f119])).
% 0.20/0.55  fof(f946,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 0.20/0.55    inference(backward_demodulation,[],[f53,f114])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f941,plain,(
% 0.20/0.55    spl4_15 | spl4_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f270,f113,f233])).
% 0.20/0.55  fof(f233,plain,(
% 0.20/0.55    spl4_15 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.55  fof(f270,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f266,f53])).
% 0.20/0.55  fof(f266,plain,(
% 0.20/0.55    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.55    inference(resolution,[],[f54,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f940,plain,(
% 0.20/0.55    ~spl4_8 | spl4_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f397,f144,f140])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    spl4_8 <=> v1_xboole_0(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.55  fof(f397,plain,(
% 0.20/0.55    v1_xboole_0(sK3) | ~v1_xboole_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f54,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.20/0.55  fof(f938,plain,(
% 0.20/0.55    ~spl4_8 | spl4_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f489,f294,f140])).
% 0.20/0.55  fof(f489,plain,(
% 0.20/0.55    ( ! [X0] : (v1_xboole_0(k7_relat_1(sK3,X0)) | ~v1_xboole_0(sK0)) )),
% 0.20/0.55    inference(resolution,[],[f182,f68])).
% 0.20/0.55  fof(f182,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f181,f52])).
% 0.20/0.55  fof(f181,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f180,f54])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.20/0.55    inference(superposition,[],[f89,f150])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.55  fof(f884,plain,(
% 0.20/0.55    spl4_3 | ~spl4_15),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f883])).
% 0.20/0.55  fof(f883,plain,(
% 0.20/0.55    $false | (spl4_3 | ~spl4_15)),
% 0.20/0.55    inference(subsumption_resolution,[],[f872,f202])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f201,f187])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    ( ! [X1] : (v1_relat_1(k7_relat_1(sK3,X1))) )),
% 0.20/0.55    inference(resolution,[],[f182,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.20/0.55    inference(resolution,[],[f189,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    ( ! [X3] : (v5_relat_1(k7_relat_1(sK3,X3),sK1)) )),
% 0.20/0.55    inference(resolution,[],[f182,f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.55  fof(f872,plain,(
% 0.20/0.55    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl4_3 | ~spl4_15)),
% 0.20/0.55    inference(resolution,[],[f780,f841])).
% 0.20/0.55  fof(f841,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.55    inference(forward_demodulation,[],[f110,f150])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f108])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.55  fof(f780,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl4_15),
% 0.20/0.55    inference(subsumption_resolution,[],[f779,f187])).
% 0.20/0.55  fof(f779,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_15),
% 0.20/0.55    inference(subsumption_resolution,[],[f775,f178])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    ( ! [X1] : (v1_funct_1(k7_relat_1(sK3,X1))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f151,f150])).
% 0.20/0.55  fof(f151,plain,(
% 0.20/0.55    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f137,f52])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) | ~v1_funct_1(sK3)) )),
% 0.20/0.55    inference(resolution,[],[f54,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f775,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_15),
% 0.20/0.55    inference(superposition,[],[f71,f771])).
% 0.20/0.55  fof(f771,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_15),
% 0.20/0.55    inference(resolution,[],[f55,f440])).
% 0.20/0.55  fof(f440,plain,(
% 0.20/0.55    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl4_15),
% 0.20/0.55    inference(subsumption_resolution,[],[f435,f132])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    v1_relat_1(sK3)),
% 0.20/0.55    inference(resolution,[],[f54,f78])).
% 0.20/0.55  fof(f435,plain,(
% 0.20/0.55    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | ~spl4_15),
% 0.20/0.55    inference(superposition,[],[f65,f432])).
% 0.20/0.55  fof(f432,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK3) | ~spl4_15),
% 0.20/0.55    inference(forward_demodulation,[],[f133,f235])).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f233])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.55    inference(resolution,[],[f54,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    r1_tarski(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.55  fof(f840,plain,(
% 0.20/0.55    spl4_2 | ~spl4_15),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f839])).
% 0.20/0.55  fof(f839,plain,(
% 0.20/0.55    $false | (spl4_2 | ~spl4_15)),
% 0.20/0.55    inference(subsumption_resolution,[],[f838,f179])).
% 0.20/0.55  fof(f838,plain,(
% 0.20/0.55    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_15),
% 0.20/0.55    inference(resolution,[],[f778,f202])).
% 0.20/0.55  fof(f778,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)) ) | ~spl4_15),
% 0.20/0.55    inference(subsumption_resolution,[],[f777,f187])).
% 0.20/0.55  fof(f777,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_15),
% 0.20/0.55    inference(subsumption_resolution,[],[f774,f178])).
% 0.20/0.55  fof(f774,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_15),
% 0.20/0.55    inference(superposition,[],[f70,f771])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f773,plain,(
% 0.20/0.55    ~spl4_6 | spl4_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f772,f127,f123])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    spl4_6 <=> r1_tarski(sK0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.55  fof(f772,plain,(
% 0.20/0.55    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 0.20/0.55    inference(resolution,[],[f55,f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(flattening,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f768,plain,(
% 0.20/0.55    spl4_3 | ~spl4_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f767])).
% 0.20/0.55  fof(f767,plain,(
% 0.20/0.55    $false | (spl4_3 | ~spl4_7)),
% 0.20/0.55    inference(subsumption_resolution,[],[f766,f182])).
% 0.20/0.55  fof(f766,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f765,f150])).
% 0.20/0.55  fof(f765,plain,(
% 0.20/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f110,f129])).
% 0.20/0.55  fof(f257,plain,(
% 0.20/0.55    ~spl4_5 | spl4_8),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f256])).
% 0.20/0.55  fof(f256,plain,(
% 0.20/0.55    $false | (~spl4_5 | spl4_8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f253,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.55  fof(f253,plain,(
% 0.20/0.55    ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | spl4_8)),
% 0.20/0.55    inference(backward_demodulation,[],[f142,f119])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    ~v1_xboole_0(sK0) | spl4_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f140])).
% 0.20/0.55  fof(f255,plain,(
% 0.20/0.55    ~spl4_5 | spl4_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f254])).
% 0.20/0.55  fof(f254,plain,(
% 0.20/0.55    $false | (~spl4_5 | spl4_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f252,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.55  fof(f252,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_6)),
% 0.20/0.55    inference(backward_demodulation,[],[f125,f119])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK2) | spl4_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f123])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    spl4_1),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f167])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    $false | spl4_1),
% 0.20/0.55    inference(resolution,[],[f151,f102])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f100])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    ~spl4_4 | spl4_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f56,f117,f113])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f57,f108,f104,f100])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (14819)------------------------------
% 0.20/0.55  % (14819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14819)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (14819)Memory used [KB]: 11001
% 0.20/0.55  % (14819)Time elapsed: 0.145 s
% 0.20/0.55  % (14819)------------------------------
% 0.20/0.55  % (14819)------------------------------
% 0.20/0.55  % (14838)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.56  % (14817)Success in time 0.199 s
%------------------------------------------------------------------------------
