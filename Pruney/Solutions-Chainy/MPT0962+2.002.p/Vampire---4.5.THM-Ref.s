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
% DateTime   : Thu Dec  3 13:00:21 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 304 expanded)
%              Number of leaves         :   19 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :  331 (1095 expanded)
%              Number of equality atoms :   45 ( 247 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f85,f112,f145,f220,f297,f325,f329])).

fof(f329,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f137,f305])).

fof(f305,plain,
    ( ! [X0,X1] : m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f304,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f304,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f303,f231])).

fof(f231,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f80,f209])).

fof(f209,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f208,f71])).

fof(f71,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f208,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f205,f131])).

fof(f131,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f205,plain,
    ( k1_xboole_0 = sK0
    | k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f52,f66])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f80,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_3
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f303,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK1),X1)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f302,f37])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r1_tarski(k2_relat_1(sK1),X1)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f281,f285])).

fof(f285,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f284,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f284,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f39,f231])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | ~ r1_tarski(k2_relat_1(sK1),X1)
      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f137,plain,
    ( ! [X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_9
  <=> ! [X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f325,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f291,f323])).

fof(f323,plain,
    ( ! [X0] : v1_funct_2(sK1,k1_xboole_0,X0)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f322,f37])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0) )
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f140,f231])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | v1_funct_2(sK1,k1_xboole_0,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl2_10
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | v1_funct_2(sK1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f291,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f212,f285])).

fof(f212,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | ~ spl2_1
    | spl2_2 ),
    inference(backward_demodulation,[],[f71,f209])).

fof(f297,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | spl2_11 ),
    inference(subsumption_resolution,[],[f288,f37])).

fof(f288,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | spl2_11 ),
    inference(backward_demodulation,[],[f144,f285])).

fof(f144,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | spl2_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_11
  <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f220,plain,
    ( ~ spl2_1
    | spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | spl2_4 ),
    inference(subsumption_resolution,[],[f213,f37])).

fof(f213,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | ~ spl2_1
    | spl2_2
    | spl2_4 ),
    inference(backward_demodulation,[],[f84,f209])).

fof(f84,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_4
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f145,plain,
    ( spl2_9
    | spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f133,f142,f139,f136])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(sK1),X0)
      | v1_funct_2(sK1,k1_xboole_0,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(resolution,[],[f106,f100])).

fof(f100,plain,(
    ! [X2,X3] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) ) ),
    inference(resolution,[],[f42,f96])).

fof(f96,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_wellord2(k1_xboole_0))))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f41,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( v1_xboole_0(k1_wellord2(k1_xboole_0))
    & v1_relat_1(k1_wellord2(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_wellord2)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK1,X1)
      | ~ r1_tarski(k1_relat_1(sK1),X1)
      | ~ r1_tarski(k2_relat_1(sK1),X0)
      | v1_funct_2(sK1,X1,X0) ) ),
    inference(resolution,[],[f103,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK1,X0)
      | v1_funct_2(sK1,X0,X1) ) ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(sK1),X1)
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f46,f32])).

fof(f112,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f110,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f110,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f105,f34])).

fof(f34,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f105,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl2_1 ),
    inference(resolution,[],[f103,f67])).

fof(f67,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f85,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f76,f82,f78])).

fof(f76,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f63,f69,f65])).

fof(f63,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(subsumption_resolution,[],[f31,f33])).

fof(f31,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (808910848)
% 0.14/0.37  ipcrm: permission denied for id (808943618)
% 0.14/0.38  ipcrm: permission denied for id (809009164)
% 0.14/0.39  ipcrm: permission denied for id (809041936)
% 0.21/0.40  ipcrm: permission denied for id (809140250)
% 0.21/0.41  ipcrm: permission denied for id (809271332)
% 0.21/0.42  ipcrm: permission denied for id (809304106)
% 0.21/0.42  ipcrm: permission denied for id (809336876)
% 0.21/0.43  ipcrm: permission denied for id (809402414)
% 0.21/0.43  ipcrm: permission denied for id (809435183)
% 0.21/0.43  ipcrm: permission denied for id (809467954)
% 0.21/0.44  ipcrm: permission denied for id (809566265)
% 0.21/0.44  ipcrm: permission denied for id (809631803)
% 0.21/0.44  ipcrm: permission denied for id (809664573)
% 0.21/0.46  ipcrm: permission denied for id (809828424)
% 0.21/0.46  ipcrm: permission denied for id (809861193)
% 0.21/0.46  ipcrm: permission denied for id (809926734)
% 0.21/0.48  ipcrm: permission denied for id (810188893)
% 0.21/0.49  ipcrm: permission denied for id (810254432)
% 0.21/0.49  ipcrm: permission denied for id (810418279)
% 0.21/0.50  ipcrm: permission denied for id (810451049)
% 0.21/0.51  ipcrm: permission denied for id (810582130)
% 0.34/0.52  ipcrm: permission denied for id (810614904)
% 0.34/0.52  ipcrm: permission denied for id (810680443)
% 0.34/0.52  ipcrm: permission denied for id (810713213)
% 0.34/0.52  ipcrm: permission denied for id (810745983)
% 0.37/0.65  % (15624)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.37/0.65  % (15632)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.37/0.67  % (15632)Refutation found. Thanks to Tanya!
% 0.37/0.67  % SZS status Theorem for theBenchmark
% 0.37/0.67  % SZS output start Proof for theBenchmark
% 0.37/0.67  fof(f330,plain,(
% 0.37/0.67    $false),
% 0.37/0.67    inference(avatar_sat_refutation,[],[f72,f85,f112,f145,f220,f297,f325,f329])).
% 0.37/0.67  fof(f329,plain,(
% 0.37/0.67    ~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_9),
% 0.37/0.67    inference(avatar_contradiction_clause,[],[f328])).
% 0.37/0.67  fof(f328,plain,(
% 0.37/0.67    $false | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_9)),
% 0.37/0.67    inference(subsumption_resolution,[],[f137,f305])).
% 0.37/0.67  fof(f305,plain,(
% 0.37/0.67    ( ! [X0,X1] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(subsumption_resolution,[],[f304,f37])).
% 0.37/0.67  fof(f37,plain,(
% 0.37/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f3])).
% 0.37/0.67  fof(f3,axiom,(
% 0.37/0.67    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.37/0.67  fof(f304,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(forward_demodulation,[],[f303,f231])).
% 0.37/0.67  fof(f231,plain,(
% 0.37/0.67    k1_xboole_0 = k2_relat_1(sK1) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(forward_demodulation,[],[f80,f209])).
% 0.37/0.67  fof(f209,plain,(
% 0.37/0.67    k1_xboole_0 = sK0 | (~spl2_1 | spl2_2)),
% 0.37/0.67    inference(subsumption_resolution,[],[f208,f71])).
% 0.37/0.67  fof(f71,plain,(
% 0.37/0.67    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl2_2),
% 0.37/0.67    inference(avatar_component_clause,[],[f69])).
% 0.37/0.67  fof(f69,plain,(
% 0.37/0.67    spl2_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.37/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.37/0.67  fof(f208,plain,(
% 0.37/0.67    k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl2_1),
% 0.37/0.67    inference(subsumption_resolution,[],[f205,f131])).
% 0.37/0.67  fof(f131,plain,(
% 0.37/0.67    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl2_1),
% 0.37/0.67    inference(resolution,[],[f66,f47])).
% 0.37/0.67  fof(f47,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f24])).
% 0.37/0.67  fof(f24,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/0.67    inference(ennf_transformation,[],[f8])).
% 0.37/0.67  fof(f8,axiom,(
% 0.37/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.37/0.67  fof(f66,plain,(
% 0.37/0.67    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl2_1),
% 0.37/0.67    inference(avatar_component_clause,[],[f65])).
% 0.37/0.67  fof(f65,plain,(
% 0.37/0.67    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.37/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.37/0.67  fof(f205,plain,(
% 0.37/0.67    k1_xboole_0 = sK0 | k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl2_1),
% 0.37/0.67    inference(resolution,[],[f52,f66])).
% 0.37/0.67  fof(f52,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f26])).
% 0.37/0.67  fof(f26,plain,(
% 0.37/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/0.67    inference(flattening,[],[f25])).
% 0.37/0.67  fof(f25,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/0.67    inference(ennf_transformation,[],[f13])).
% 0.37/0.67  fof(f13,axiom,(
% 0.37/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.37/0.67  fof(f80,plain,(
% 0.37/0.67    sK0 = k2_relat_1(sK1) | ~spl2_3),
% 0.37/0.67    inference(avatar_component_clause,[],[f78])).
% 0.37/0.67  fof(f78,plain,(
% 0.37/0.67    spl2_3 <=> sK0 = k2_relat_1(sK1)),
% 0.37/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.37/0.67  fof(f303,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK1),X1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(subsumption_resolution,[],[f302,f37])).
% 0.37/0.67  fof(f302,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(sK1),X1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(forward_demodulation,[],[f281,f285])).
% 0.37/0.67  fof(f285,plain,(
% 0.37/0.67    k1_xboole_0 = k1_relat_1(sK1) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(subsumption_resolution,[],[f284,f32])).
% 0.37/0.67  fof(f32,plain,(
% 0.37/0.67    v1_relat_1(sK1)),
% 0.37/0.67    inference(cnf_transformation,[],[f18])).
% 0.37/0.67  fof(f18,plain,(
% 0.37/0.67    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.37/0.67    inference(flattening,[],[f17])).
% 0.37/0.67  fof(f17,plain,(
% 0.37/0.67    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.37/0.67    inference(ennf_transformation,[],[f15])).
% 0.37/0.67  fof(f15,negated_conjecture,(
% 0.37/0.67    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.37/0.67    inference(negated_conjecture,[],[f14])).
% 0.37/0.67  fof(f14,conjecture,(
% 0.37/0.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.37/0.67  fof(f284,plain,(
% 0.37/0.67    ~v1_relat_1(sK1) | k1_xboole_0 = k1_relat_1(sK1) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(trivial_inequality_removal,[],[f283])).
% 0.37/0.67  fof(f283,plain,(
% 0.37/0.67    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK1) | k1_xboole_0 = k1_relat_1(sK1) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(superposition,[],[f39,f231])).
% 0.37/0.67  fof(f39,plain,(
% 0.37/0.67    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f19])).
% 0.37/0.67  fof(f19,plain,(
% 0.37/0.67    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.37/0.67    inference(ennf_transformation,[],[f6])).
% 0.37/0.67  fof(f6,axiom,(
% 0.37/0.67    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.37/0.67  fof(f281,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X0) | ~r1_tarski(k2_relat_1(sK1),X1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/0.67    inference(resolution,[],[f32,f46])).
% 0.37/0.67  fof(f46,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/0.67    inference(cnf_transformation,[],[f23])).
% 0.37/0.67  fof(f23,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.37/0.67    inference(flattening,[],[f22])).
% 0.37/0.67  fof(f22,plain,(
% 0.37/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.37/0.67    inference(ennf_transformation,[],[f9])).
% 0.37/0.67  fof(f9,axiom,(
% 0.37/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.37/0.67  fof(f137,plain,(
% 0.37/0.67    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl2_9),
% 0.37/0.67    inference(avatar_component_clause,[],[f136])).
% 0.37/0.67  fof(f136,plain,(
% 0.37/0.67    spl2_9 <=> ! [X1] : ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))),
% 0.37/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.37/0.67  fof(f325,plain,(
% 0.37/0.67    ~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_10),
% 0.37/0.67    inference(avatar_contradiction_clause,[],[f324])).
% 0.37/0.67  fof(f324,plain,(
% 0.37/0.67    $false | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_10)),
% 0.37/0.67    inference(subsumption_resolution,[],[f291,f323])).
% 0.37/0.67  fof(f323,plain,(
% 0.37/0.67    ( ! [X0] : (v1_funct_2(sK1,k1_xboole_0,X0)) ) | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_10)),
% 0.37/0.67    inference(subsumption_resolution,[],[f322,f37])).
% 0.37/0.67  fof(f322,plain,(
% 0.37/0.67    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0)) ) | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_10)),
% 0.37/0.67    inference(forward_demodulation,[],[f140,f231])).
% 0.37/0.67  fof(f140,plain,(
% 0.37/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | v1_funct_2(sK1,k1_xboole_0,X0)) ) | ~spl2_10),
% 0.37/0.67    inference(avatar_component_clause,[],[f139])).
% 0.37/0.67  fof(f139,plain,(
% 0.37/0.67    spl2_10 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | v1_funct_2(sK1,k1_xboole_0,X0))),
% 0.37/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.37/0.67  fof(f291,plain,(
% 0.37/0.67    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.37/0.67    inference(backward_demodulation,[],[f212,f285])).
% 0.37/0.67  fof(f212,plain,(
% 0.37/0.67    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (~spl2_1 | spl2_2)),
% 0.37/0.67    inference(backward_demodulation,[],[f71,f209])).
% 0.37/0.67  fof(f297,plain,(
% 0.37/0.67    ~spl2_1 | spl2_2 | ~spl2_3 | spl2_11),
% 0.37/0.67    inference(avatar_contradiction_clause,[],[f296])).
% 0.37/0.67  fof(f296,plain,(
% 0.37/0.67    $false | (~spl2_1 | spl2_2 | ~spl2_3 | spl2_11)),
% 0.37/0.67    inference(subsumption_resolution,[],[f288,f37])).
% 0.37/0.67  fof(f288,plain,(
% 0.37/0.67    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl2_1 | spl2_2 | ~spl2_3 | spl2_11)),
% 0.37/0.67    inference(backward_demodulation,[],[f144,f285])).
% 0.37/0.67  fof(f144,plain,(
% 0.37/0.67    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | spl2_11),
% 0.37/0.67    inference(avatar_component_clause,[],[f142])).
% 0.37/0.67  fof(f142,plain,(
% 0.37/0.67    spl2_11 <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.37/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.37/0.67  fof(f220,plain,(
% 0.37/0.67    ~spl2_1 | spl2_2 | spl2_4),
% 0.37/0.67    inference(avatar_contradiction_clause,[],[f219])).
% 0.37/0.67  fof(f219,plain,(
% 0.37/0.67    $false | (~spl2_1 | spl2_2 | spl2_4)),
% 0.37/0.67    inference(subsumption_resolution,[],[f213,f37])).
% 0.37/0.67  fof(f213,plain,(
% 0.37/0.67    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | (~spl2_1 | spl2_2 | spl2_4)),
% 0.37/0.67    inference(backward_demodulation,[],[f84,f209])).
% 0.37/0.67  fof(f84,plain,(
% 0.37/0.67    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl2_4),
% 0.37/0.67    inference(avatar_component_clause,[],[f82])).
% 0.37/0.67  fof(f82,plain,(
% 0.37/0.67    spl2_4 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.37/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.37/0.67  fof(f145,plain,(
% 0.37/0.67    spl2_9 | spl2_10 | ~spl2_11),
% 0.37/0.67    inference(avatar_split_clause,[],[f133,f142,f139,f136])).
% 0.37/0.67  fof(f133,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~r1_tarski(k2_relat_1(sK1),X0) | v1_funct_2(sK1,k1_xboole_0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.37/0.67    inference(resolution,[],[f106,f100])).
% 0.37/0.67  fof(f100,plain,(
% 0.37/0.67    ( ! [X2,X3] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))) )),
% 0.37/0.67    inference(resolution,[],[f42,f96])).
% 0.37/0.67  fof(f96,plain,(
% 0.37/0.67    v1_xboole_0(k1_xboole_0)),
% 0.37/0.67    inference(resolution,[],[f95,f38])).
% 0.37/0.67  fof(f38,plain,(
% 0.37/0.67    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.37/0.67    inference(cnf_transformation,[],[f4])).
% 0.37/0.67  fof(f4,axiom,(
% 0.37/0.67    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.37/0.67  fof(f95,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_wellord2(k1_xboole_0)))) | v1_xboole_0(X0)) )),
% 0.37/0.67    inference(resolution,[],[f41,f36])).
% 0.37/0.67  fof(f36,plain,(
% 0.37/0.67    v1_xboole_0(k1_wellord2(k1_xboole_0))),
% 0.37/0.67    inference(cnf_transformation,[],[f10])).
% 0.37/0.67  fof(f10,axiom,(
% 0.37/0.67    v1_xboole_0(k1_wellord2(k1_xboole_0)) & v1_relat_1(k1_wellord2(k1_xboole_0))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_wellord2)).
% 0.37/0.67  fof(f41,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f20])).
% 0.37/0.67  fof(f20,plain,(
% 0.37/0.67    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.37/0.67    inference(ennf_transformation,[],[f7])).
% 0.37/0.67  fof(f7,axiom,(
% 0.37/0.67    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.37/0.67  fof(f42,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f21])).
% 0.37/0.67  fof(f21,plain,(
% 0.37/0.67    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.37/0.67    inference(ennf_transformation,[],[f12])).
% 0.37/0.67  fof(f12,axiom,(
% 0.37/0.67    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.37/0.67  fof(f106,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~v1_partfun1(sK1,X1) | ~r1_tarski(k1_relat_1(sK1),X1) | ~r1_tarski(k2_relat_1(sK1),X0) | v1_funct_2(sK1,X1,X0)) )),
% 0.37/0.67    inference(resolution,[],[f103,f102])).
% 0.37/0.67  fof(f102,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK1,X0) | v1_funct_2(sK1,X0,X1)) )),
% 0.37/0.67    inference(resolution,[],[f54,f33])).
% 0.37/0.67  fof(f33,plain,(
% 0.37/0.67    v1_funct_1(sK1)),
% 0.37/0.67    inference(cnf_transformation,[],[f18])).
% 0.37/0.67  fof(f54,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  fof(f28,plain,(
% 0.37/0.67    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/0.67    inference(flattening,[],[f27])).
% 0.37/0.67  fof(f27,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/0.67    inference(ennf_transformation,[],[f11])).
% 0.37/0.67  fof(f11,axiom,(
% 0.37/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.37/0.67  fof(f103,plain,(
% 0.37/0.67    ( ! [X0,X1] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(sK1),X1) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 0.37/0.67    inference(resolution,[],[f46,f32])).
% 0.37/0.67  fof(f112,plain,(
% 0.37/0.67    spl2_1),
% 0.37/0.67    inference(avatar_contradiction_clause,[],[f111])).
% 0.37/0.67  fof(f111,plain,(
% 0.37/0.67    $false | spl2_1),
% 0.37/0.67    inference(subsumption_resolution,[],[f110,f56])).
% 0.37/0.67  fof(f56,plain,(
% 0.37/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.37/0.67    inference(equality_resolution,[],[f44])).
% 0.37/0.67  fof(f44,plain,(
% 0.37/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.37/0.67    inference(cnf_transformation,[],[f1])).
% 0.37/0.67  fof(f1,axiom,(
% 0.37/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.37/0.67  fof(f110,plain,(
% 0.37/0.67    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl2_1),
% 0.37/0.67    inference(subsumption_resolution,[],[f105,f34])).
% 0.37/0.67  fof(f34,plain,(
% 0.37/0.67    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.37/0.67    inference(cnf_transformation,[],[f18])).
% 0.37/0.67  fof(f105,plain,(
% 0.37/0.67    ~r1_tarski(k2_relat_1(sK1),sK0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl2_1),
% 0.37/0.67    inference(resolution,[],[f103,f67])).
% 0.37/0.67  fof(f67,plain,(
% 0.37/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl2_1),
% 0.37/0.67    inference(avatar_component_clause,[],[f65])).
% 0.37/0.67  fof(f85,plain,(
% 0.37/0.67    spl2_3 | ~spl2_4),
% 0.37/0.67    inference(avatar_split_clause,[],[f76,f82,f78])).
% 0.37/0.67  fof(f76,plain,(
% 0.37/0.67    ~r1_tarski(sK0,k2_relat_1(sK1)) | sK0 = k2_relat_1(sK1)),
% 0.37/0.67    inference(resolution,[],[f45,f34])).
% 0.37/0.67  fof(f45,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.37/0.67    inference(cnf_transformation,[],[f1])).
% 0.37/0.67  fof(f72,plain,(
% 0.37/0.67    ~spl2_1 | ~spl2_2),
% 0.37/0.67    inference(avatar_split_clause,[],[f63,f69,f65])).
% 0.37/0.67  fof(f63,plain,(
% 0.37/0.67    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.37/0.67    inference(subsumption_resolution,[],[f31,f33])).
% 0.37/0.67  fof(f31,plain,(
% 0.37/0.67    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.37/0.67    inference(cnf_transformation,[],[f18])).
% 0.37/0.67  % SZS output end Proof for theBenchmark
% 0.37/0.67  % (15632)------------------------------
% 0.37/0.67  % (15632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (15632)Termination reason: Refutation
% 0.37/0.67  
% 0.37/0.67  % (15632)Memory used [KB]: 10746
% 0.37/0.67  % (15632)Time elapsed: 0.024 s
% 0.37/0.67  % (15632)------------------------------
% 0.37/0.67  % (15632)------------------------------
% 0.37/0.67  % (15471)Success in time 0.309 s
%------------------------------------------------------------------------------
