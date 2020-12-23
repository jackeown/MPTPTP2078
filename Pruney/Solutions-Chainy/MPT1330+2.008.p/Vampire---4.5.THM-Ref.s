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
% DateTime   : Thu Dec  3 13:13:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 384 expanded)
%              Number of leaves         :   47 ( 164 expanded)
%              Depth                    :   10
%              Number of atoms          :  566 (1386 expanded)
%              Number of equality atoms :  116 ( 390 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f82,f86,f90,f94,f98,f102,f106,f114,f118,f126,f151,f157,f165,f202,f211,f245,f248,f252,f258,f273,f279,f288,f296,f357,f366,f373,f425,f448])).

fof(f448,plain,
    ( ~ spl3_17
    | ~ spl3_9
    | spl3_45 ),
    inference(avatar_split_clause,[],[f446,f423,f104,f161])).

fof(f161,plain,
    ( spl3_17
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f104,plain,
    ( spl3_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f423,plain,
    ( spl3_45
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f446,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9
    | spl3_45 ),
    inference(superposition,[],[f428,f144])).

fof(f144,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(resolution,[],[f108,f105])).

fof(f105,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f428,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | spl3_45 ),
    inference(trivial_inequality_removal,[],[f427])).

fof(f427,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | spl3_45 ),
    inference(superposition,[],[f424,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(resolution,[],[f180,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(global_subsumption,[],[f58,f66,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f424,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl3_45 ),
    inference(avatar_component_clause,[],[f423])).

fof(f425,plain,
    ( ~ spl3_45
    | spl3_39
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f385,f371,f355,f423])).

fof(f355,plain,
    ( spl3_39
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f371,plain,
    ( spl3_40
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f385,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl3_39
    | ~ spl3_40 ),
    inference(superposition,[],[f356,f372])).

fof(f372,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f371])).

fof(f356,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl3_39 ),
    inference(avatar_component_clause,[],[f355])).

fof(f373,plain,
    ( spl3_40
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f369,f306,f371])).

fof(f306,plain,
    ( spl3_34
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f369,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_34 ),
    inference(resolution,[],[f363,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f64,f55])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f363,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f306])).

fof(f366,plain,
    ( spl3_34
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f365,f129,f104,f77,f306])).

fof(f77,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f129,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f365,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f361,f144])).

fof(f361,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(superposition,[],[f130,f295])).

fof(f295,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f357,plain,
    ( ~ spl3_39
    | ~ spl3_3
    | spl3_20 ),
    inference(avatar_split_clause,[],[f353,f209,f80,f355])).

fof(f80,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f209,plain,
    ( spl3_20
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f353,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_3
    | spl3_20 ),
    inference(superposition,[],[f210,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f210,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f296,plain,
    ( spl3_2
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f294,f270,f77])).

fof(f270,plain,
    ( spl3_29
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f294,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_29 ),
    inference(resolution,[],[f271,f54])).

fof(f271,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f270])).

fof(f288,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f279,plain,
    ( ~ spl3_13
    | spl3_28 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl3_13
    | spl3_28 ),
    inference(subsumption_resolution,[],[f130,f275])).

fof(f275,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | spl3_28 ),
    inference(resolution,[],[f268,f180])).

fof(f268,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl3_28
  <=> r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f273,plain,
    ( ~ spl3_28
    | ~ spl3_13
    | spl3_29
    | spl3_20
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f265,f256,f116,f112,f88,f209,f270,f129,f267])).

fof(f88,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( spl3_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f116,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f256,plain,
    ( spl3_27
  <=> ! [X1,X0] :
        ( k1_relat_1(sK2) = X0
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f265,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f264,f117])).

fof(f117,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f264,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f263,f113])).

fof(f113,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f263,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f262,f117])).

fof(f262,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f261,f113])).

fof(f261,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f259,f117])).

fof(f259,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_27 ),
    inference(resolution,[],[f257,f89])).

fof(f89,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | k1_relat_1(sK2) = X0 )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl3_25
    | spl3_27
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f253,f243,f256,f240])).

fof(f240,plain,
    ( spl3_25
  <=> ! [X3,X2] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f243,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f253,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relat_1(sK2) = X0
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl3_26 ),
    inference(resolution,[],[f244,f167])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_relat_1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f59,f66])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f243])).

fof(f252,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f251,f116,f112,f84,f129])).

fof(f84,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f251,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f250,f117])).

fof(f250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f85,f113])).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f248,plain,
    ( ~ spl3_4
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f85,f241])).

fof(f241,plain,
    ( ! [X2,X3] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f245,plain,
    ( spl3_25
    | spl3_26
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f238,f92,f243,f240])).

fof(f92,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f238,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl3_6 ),
    inference(resolution,[],[f237,f174])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f62,f66])).

% (5392)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f237,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f57,f93])).

fof(f93,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f211,plain,
    ( ~ spl3_19
    | ~ spl3_20
    | spl3_18 ),
    inference(avatar_split_clause,[],[f204,f200,f209,f206])).

fof(f206,plain,
    ( spl3_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f200,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f204,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | spl3_18 ),
    inference(inner_rewriting,[],[f203])).

fof(f203,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_18 ),
    inference(superposition,[],[f201,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f201,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( ~ spl3_13
    | ~ spl3_18
    | spl3_12 ),
    inference(avatar_split_clause,[],[f197,f124,f200,f129])).

fof(f124,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f197,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_12 ),
    inference(superposition,[],[f125,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f125,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f165,plain,
    ( spl3_17
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f164,f155,f104,f161])).

fof(f155,plain,
    ( spl3_16
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f164,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f159,f144])).

fof(f159,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_16 ),
    inference(superposition,[],[f52,f156])).

fof(f156,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f157,plain,
    ( spl3_16
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f152,f149,f155])).

fof(f149,plain,
    ( spl3_15
  <=> m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f152,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_15 ),
    inference(resolution,[],[f143,f150])).

fof(f150,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl3_15
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f147,f104,f149])).

fof(f147,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9 ),
    inference(superposition,[],[f52,f144])).

fof(f126,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f122,f116,f112,f73,f124])).

fof(f73,plain,
    ( spl3_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f122,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f119,f117])).

fof(f119,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f74,f113])).

fof(f74,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f118,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f110,f100,f116])).

fof(f100,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f110,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f53,f101])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f114,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f109,f96,f112])).

fof(f96,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f109,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f53,f97])).

fof(f97,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f106,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f50,f104])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f102,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f43,f100])).

fof(f43,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f98,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f47,f84])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f48,f80,f77])).

fof(f48,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f49,f73])).

fof(f49,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (5398)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.45  % (5390)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.46  % (5394)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.46  % (5402)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.46  % (5386)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.47  % (5390)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f450,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f75,f82,f86,f90,f94,f98,f102,f106,f114,f118,f126,f151,f157,f165,f202,f211,f245,f248,f252,f258,f273,f279,f288,f296,f357,f366,f373,f425,f448])).
% 0.19/0.47  fof(f448,plain,(
% 0.19/0.47    ~spl3_17 | ~spl3_9 | spl3_45),
% 0.19/0.47    inference(avatar_split_clause,[],[f446,f423,f104,f161])).
% 0.19/0.47  fof(f161,plain,(
% 0.19/0.47    spl3_17 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.47  fof(f104,plain,(
% 0.19/0.47    spl3_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.47  fof(f423,plain,(
% 0.19/0.47    spl3_45 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.19/0.47  fof(f446,plain,(
% 0.19/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_9 | spl3_45)),
% 0.19/0.47    inference(superposition,[],[f428,f144])).
% 0.19/0.47  fof(f144,plain,(
% 0.19/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_9),
% 0.19/0.47    inference(resolution,[],[f108,f105])).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 0.19/0.47    inference(avatar_component_clause,[],[f104])).
% 0.19/0.47  fof(f108,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.19/0.47    inference(resolution,[],[f60,f54])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.19/0.47  fof(f428,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | spl3_45),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f427])).
% 0.19/0.47  fof(f427,plain,(
% 0.19/0.47    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | spl3_45),
% 0.19/0.47    inference(superposition,[],[f424,f181])).
% 0.19/0.47  fof(f181,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_xboole_0 = k1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.19/0.47    inference(resolution,[],[f180,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.19/0.47  fof(f180,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.19/0.47    inference(global_subsumption,[],[f58,f66,f68])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f10])).
% 0.19/0.47  fof(f10,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.47  fof(f424,plain,(
% 0.19/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl3_45),
% 0.19/0.47    inference(avatar_component_clause,[],[f423])).
% 0.19/0.47  fof(f425,plain,(
% 0.19/0.47    ~spl3_45 | spl3_39 | ~spl3_40),
% 0.19/0.47    inference(avatar_split_clause,[],[f385,f371,f355,f423])).
% 0.19/0.47  fof(f355,plain,(
% 0.19/0.47    spl3_39 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.19/0.47  fof(f371,plain,(
% 0.19/0.47    spl3_40 <=> k1_xboole_0 = sK2),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.19/0.47  fof(f385,plain,(
% 0.19/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (spl3_39 | ~spl3_40)),
% 0.19/0.47    inference(superposition,[],[f356,f372])).
% 0.19/0.47  fof(f372,plain,(
% 0.19/0.47    k1_xboole_0 = sK2 | ~spl3_40),
% 0.19/0.47    inference(avatar_component_clause,[],[f371])).
% 0.19/0.47  fof(f356,plain,(
% 0.19/0.47    k1_xboole_0 != k1_relat_1(sK2) | spl3_39),
% 0.19/0.47    inference(avatar_component_clause,[],[f355])).
% 0.19/0.47  fof(f373,plain,(
% 0.19/0.47    spl3_40 | ~spl3_34),
% 0.19/0.47    inference(avatar_split_clause,[],[f369,f306,f371])).
% 0.19/0.47  fof(f306,plain,(
% 0.19/0.47    spl3_34 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.19/0.47  fof(f369,plain,(
% 0.19/0.47    k1_xboole_0 = sK2 | ~spl3_34),
% 0.19/0.47    inference(resolution,[],[f363,f143])).
% 0.19/0.47  fof(f143,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.19/0.47    inference(resolution,[],[f64,f55])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.47    inference(nnf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.47  fof(f363,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_34),
% 0.19/0.47    inference(avatar_component_clause,[],[f306])).
% 0.19/0.47  fof(f366,plain,(
% 0.19/0.47    spl3_34 | ~spl3_2 | ~spl3_9 | ~spl3_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f365,f129,f104,f77,f306])).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.47  fof(f365,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_2 | ~spl3_9 | ~spl3_13)),
% 0.19/0.47    inference(forward_demodulation,[],[f361,f144])).
% 0.19/0.47  fof(f361,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_2 | ~spl3_13)),
% 0.19/0.47    inference(superposition,[],[f130,f295])).
% 0.19/0.47  fof(f295,plain,(
% 0.19/0.47    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f77])).
% 0.19/0.47  fof(f130,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.19/0.47    inference(avatar_component_clause,[],[f129])).
% 0.19/0.47  fof(f357,plain,(
% 0.19/0.47    ~spl3_39 | ~spl3_3 | spl3_20),
% 0.19/0.47    inference(avatar_split_clause,[],[f353,f209,f80,f355])).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    spl3_3 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.47  fof(f209,plain,(
% 0.19/0.47    spl3_20 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.19/0.47  fof(f353,plain,(
% 0.19/0.47    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_3 | spl3_20)),
% 0.19/0.47    inference(superposition,[],[f210,f81])).
% 0.19/0.47  fof(f81,plain,(
% 0.19/0.47    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f80])).
% 0.19/0.47  fof(f210,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_20),
% 0.19/0.47    inference(avatar_component_clause,[],[f209])).
% 0.19/0.47  fof(f296,plain,(
% 0.19/0.47    spl3_2 | ~spl3_29),
% 0.19/0.47    inference(avatar_split_clause,[],[f294,f270,f77])).
% 0.19/0.47  fof(f270,plain,(
% 0.19/0.47    spl3_29 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.19/0.47  fof(f294,plain,(
% 0.19/0.47    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_29),
% 0.19/0.47    inference(resolution,[],[f271,f54])).
% 0.19/0.47  fof(f271,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_29),
% 0.19/0.47    inference(avatar_component_clause,[],[f270])).
% 0.19/0.47  fof(f288,plain,(
% 0.19/0.47    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  fof(f279,plain,(
% 0.19/0.47    ~spl3_13 | spl3_28),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f278])).
% 0.19/0.47  fof(f278,plain,(
% 0.19/0.47    $false | (~spl3_13 | spl3_28)),
% 0.19/0.47    inference(subsumption_resolution,[],[f130,f275])).
% 0.19/0.47  fof(f275,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | spl3_28),
% 0.19/0.47    inference(resolution,[],[f268,f180])).
% 0.19/0.47  fof(f268,plain,(
% 0.19/0.47    ~r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) | spl3_28),
% 0.19/0.47    inference(avatar_component_clause,[],[f267])).
% 0.19/0.47  fof(f267,plain,(
% 0.19/0.47    spl3_28 <=> r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.19/0.47  fof(f273,plain,(
% 0.19/0.47    ~spl3_28 | ~spl3_13 | spl3_29 | spl3_20 | ~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_27),
% 0.19/0.47    inference(avatar_split_clause,[],[f265,f256,f116,f112,f88,f209,f270,f129,f267])).
% 0.19/0.47  fof(f88,plain,(
% 0.19/0.47    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.47  fof(f112,plain,(
% 0.19/0.47    spl3_10 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    spl3_11 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.47  fof(f256,plain,(
% 0.19/0.47    spl3_27 <=> ! [X1,X0] : (k1_relat_1(sK2) = X0 | ~r1_tarski(k1_relat_1(sK2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.19/0.47  fof(f265,plain,(
% 0.19/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_27)),
% 0.19/0.47    inference(forward_demodulation,[],[f264,f117])).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_11),
% 0.19/0.47    inference(avatar_component_clause,[],[f116])).
% 0.19/0.47  fof(f264,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) | u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_27)),
% 0.19/0.47    inference(forward_demodulation,[],[f263,f113])).
% 0.19/0.47  fof(f113,plain,(
% 0.19/0.47    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_10),
% 0.19/0.47    inference(avatar_component_clause,[],[f112])).
% 0.19/0.47  fof(f263,plain,(
% 0.19/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_27)),
% 0.19/0.47    inference(forward_demodulation,[],[f262,f117])).
% 0.19/0.47  fof(f262,plain,(
% 0.19/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_27)),
% 0.19/0.47    inference(forward_demodulation,[],[f261,f113])).
% 0.19/0.47  fof(f261,plain,(
% 0.19/0.47    ~r1_tarski(k1_relat_1(sK2),k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_5 | ~spl3_11 | ~spl3_27)),
% 0.19/0.47    inference(forward_demodulation,[],[f259,f117])).
% 0.19/0.47  fof(f259,plain,(
% 0.19/0.47    ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_5 | ~spl3_27)),
% 0.19/0.47    inference(resolution,[],[f257,f89])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.19/0.47    inference(avatar_component_clause,[],[f88])).
% 0.19/0.47  fof(f257,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~r1_tarski(k1_relat_1(sK2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | k1_relat_1(sK2) = X0) ) | ~spl3_27),
% 0.19/0.47    inference(avatar_component_clause,[],[f256])).
% 0.19/0.47  fof(f258,plain,(
% 0.19/0.47    spl3_25 | spl3_27 | ~spl3_26),
% 0.19/0.47    inference(avatar_split_clause,[],[f253,f243,f256,f240])).
% 0.19/0.47  fof(f240,plain,(
% 0.19/0.47    spl3_25 <=> ! [X3,X2] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.19/0.47  fof(f243,plain,(
% 0.19/0.47    spl3_26 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.19/0.47  fof(f253,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (k1_relat_1(sK2) = X0 | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(sK2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl3_26),
% 0.19/0.47    inference(resolution,[],[f244,f167])).
% 0.19/0.47  fof(f167,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (v4_relat_1(X0,X1) | ~r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.19/0.47    inference(resolution,[],[f59,f66])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f244,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_26),
% 0.19/0.47    inference(avatar_component_clause,[],[f243])).
% 0.19/0.47  fof(f252,plain,(
% 0.19/0.47    spl3_13 | ~spl3_4 | ~spl3_10 | ~spl3_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f251,f116,f112,f84,f129])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.47  fof(f251,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.19/0.47    inference(forward_demodulation,[],[f250,f117])).
% 0.19/0.47  fof(f250,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10)),
% 0.19/0.47    inference(forward_demodulation,[],[f85,f113])).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.19/0.47    inference(avatar_component_clause,[],[f84])).
% 0.19/0.47  fof(f248,plain,(
% 0.19/0.47    ~spl3_4 | ~spl3_25),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f246])).
% 0.19/0.47  fof(f246,plain,(
% 0.19/0.47    $false | (~spl3_4 | ~spl3_25)),
% 0.19/0.47    inference(subsumption_resolution,[],[f85,f241])).
% 0.19/0.47  fof(f241,plain,(
% 0.19/0.47    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl3_25),
% 0.19/0.47    inference(avatar_component_clause,[],[f240])).
% 0.19/0.47  fof(f245,plain,(
% 0.19/0.47    spl3_25 | spl3_26 | ~spl3_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f238,f92,f243,f240])).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    spl3_6 <=> v1_funct_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.47  fof(f238,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl3_6),
% 0.19/0.47    inference(resolution,[],[f237,f174])).
% 0.19/0.47  fof(f174,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.19/0.47    inference(resolution,[],[f62,f66])).
% 0.19/0.47  % (5392)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f41])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.19/0.47  fof(f237,plain,(
% 0.19/0.47    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl3_6),
% 0.19/0.47    inference(resolution,[],[f57,f93])).
% 0.19/0.47  fof(f93,plain,(
% 0.19/0.47    v1_funct_1(sK2) | ~spl3_6),
% 0.19/0.47    inference(avatar_component_clause,[],[f92])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.47    inference(flattening,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,axiom,(
% 0.19/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.47  fof(f211,plain,(
% 0.19/0.47    ~spl3_19 | ~spl3_20 | spl3_18),
% 0.19/0.47    inference(avatar_split_clause,[],[f204,f200,f209,f206])).
% 0.19/0.47  fof(f206,plain,(
% 0.19/0.47    spl3_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.19/0.47  fof(f200,plain,(
% 0.19/0.47    spl3_18 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.19/0.47  fof(f204,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | spl3_18),
% 0.19/0.47    inference(inner_rewriting,[],[f203])).
% 0.19/0.47  fof(f203,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_18),
% 0.19/0.47    inference(superposition,[],[f201,f67])).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.47  fof(f201,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | spl3_18),
% 0.19/0.47    inference(avatar_component_clause,[],[f200])).
% 0.19/0.47  fof(f202,plain,(
% 0.19/0.47    ~spl3_13 | ~spl3_18 | spl3_12),
% 0.19/0.47    inference(avatar_split_clause,[],[f197,f124,f200,f129])).
% 0.19/0.47  fof(f124,plain,(
% 0.19/0.47    spl3_12 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.47  fof(f197,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_12),
% 0.19/0.47    inference(superposition,[],[f125,f70])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.19/0.47  fof(f125,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_12),
% 0.19/0.47    inference(avatar_component_clause,[],[f124])).
% 0.19/0.47  fof(f165,plain,(
% 0.19/0.47    spl3_17 | ~spl3_9 | ~spl3_16),
% 0.19/0.47    inference(avatar_split_clause,[],[f164,f155,f104,f161])).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    spl3_16 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.47  fof(f164,plain,(
% 0.19/0.47    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_9 | ~spl3_16)),
% 0.19/0.47    inference(forward_demodulation,[],[f159,f144])).
% 0.19/0.47  fof(f159,plain,(
% 0.19/0.47    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_16),
% 0.19/0.47    inference(superposition,[],[f52,f156])).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_16),
% 0.19/0.47    inference(avatar_component_clause,[],[f155])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,axiom,(
% 0.19/0.47    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.19/0.47  fof(f157,plain,(
% 0.19/0.47    spl3_16 | ~spl3_15),
% 0.19/0.47    inference(avatar_split_clause,[],[f152,f149,f155])).
% 0.19/0.47  fof(f149,plain,(
% 0.19/0.47    spl3_15 <=> m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.47  fof(f152,plain,(
% 0.19/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_15),
% 0.19/0.47    inference(resolution,[],[f143,f150])).
% 0.19/0.47  fof(f150,plain,(
% 0.19/0.47    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_15),
% 0.19/0.47    inference(avatar_component_clause,[],[f149])).
% 0.19/0.47  fof(f151,plain,(
% 0.19/0.47    spl3_15 | ~spl3_9),
% 0.19/0.47    inference(avatar_split_clause,[],[f147,f104,f149])).
% 0.19/0.47  fof(f147,plain,(
% 0.19/0.47    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_9),
% 0.19/0.47    inference(superposition,[],[f52,f144])).
% 0.19/0.47  fof(f126,plain,(
% 0.19/0.47    ~spl3_12 | spl3_1 | ~spl3_10 | ~spl3_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f122,f116,f112,f73,f124])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    spl3_1 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.47  fof(f122,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_10 | ~spl3_11)),
% 0.19/0.47    inference(forward_demodulation,[],[f119,f117])).
% 0.19/0.47  fof(f119,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_10)),
% 0.19/0.47    inference(superposition,[],[f74,f113])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f73])).
% 0.19/0.47  fof(f118,plain,(
% 0.19/0.47    spl3_11 | ~spl3_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f110,f100,f116])).
% 0.19/0.47  fof(f100,plain,(
% 0.19/0.47    spl3_8 <=> l1_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.47  fof(f110,plain,(
% 0.19/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.19/0.47    inference(resolution,[],[f53,f101])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    l1_struct_0(sK0) | ~spl3_8),
% 0.19/0.47    inference(avatar_component_clause,[],[f100])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,axiom,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.47  fof(f114,plain,(
% 0.19/0.47    spl3_10 | ~spl3_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f109,f96,f112])).
% 0.19/0.47  fof(f96,plain,(
% 0.19/0.47    spl3_7 <=> l1_struct_0(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.47  fof(f109,plain,(
% 0.19/0.47    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.19/0.47    inference(resolution,[],[f53,f97])).
% 0.19/0.47  fof(f97,plain,(
% 0.19/0.47    l1_struct_0(sK1) | ~spl3_7),
% 0.19/0.47    inference(avatar_component_clause,[],[f96])).
% 0.19/0.47  fof(f106,plain,(
% 0.19/0.47    spl3_9),
% 0.19/0.47    inference(avatar_split_clause,[],[f50,f104])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    v1_xboole_0(k1_xboole_0)),
% 0.19/0.47    inference(cnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    v1_xboole_0(k1_xboole_0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.47  fof(f102,plain,(
% 0.19/0.47    spl3_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f43,f100])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    l1_struct_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f39])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38,f37,f36])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,negated_conjecture,(
% 0.19/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.19/0.47    inference(negated_conjecture,[],[f17])).
% 0.19/0.47  fof(f17,conjecture,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 0.19/0.47  fof(f98,plain,(
% 0.19/0.47    spl3_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f44,f96])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    l1_struct_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f39])).
% 0.19/0.47  fof(f94,plain,(
% 0.19/0.47    spl3_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f45,f92])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    v1_funct_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f39])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    spl3_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f46,f88])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f39])).
% 0.19/0.47  fof(f86,plain,(
% 0.19/0.47    spl3_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f47,f84])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.47    inference(cnf_transformation,[],[f39])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    ~spl3_2 | spl3_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f48,f80,f77])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f39])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    ~spl3_1),
% 0.19/0.47    inference(avatar_split_clause,[],[f49,f73])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f39])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (5390)------------------------------
% 0.19/0.47  % (5390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (5390)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (5390)Memory used [KB]: 10874
% 0.19/0.47  % (5390)Time elapsed: 0.061 s
% 0.19/0.47  % (5390)------------------------------
% 0.19/0.47  % (5390)------------------------------
% 0.19/0.48  % (5396)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (5383)Success in time 0.129 s
%------------------------------------------------------------------------------
