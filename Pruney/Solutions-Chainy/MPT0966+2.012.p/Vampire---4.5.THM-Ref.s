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
% DateTime   : Thu Dec  3 13:00:39 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  241 (1053 expanded)
%              Number of leaves         :   38 ( 297 expanded)
%              Depth                    :   20
%              Number of atoms          :  770 (4725 expanded)
%              Number of equality atoms :  162 (1280 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1075,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f146,f148,f196,f213,f230,f307,f310,f353,f407,f417,f441,f485,f493,f518,f527,f654,f706,f878,f1074])).

fof(f1074,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | ~ spl8_15
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f1073])).

fof(f1073,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_15
    | spl8_20 ),
    inference(subsumption_resolution,[],[f1072,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1072,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_15
    | spl8_20 ),
    inference(subsumption_resolution,[],[f1071,f951])).

fof(f951,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_15
    | spl8_20 ),
    inference(backward_demodulation,[],[f938,f945])).

fof(f945,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_4
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f944,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f944,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f229,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f229,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl8_15
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f938,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ spl8_5
    | spl8_20 ),
    inference(backward_demodulation,[],[f374,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f374,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl8_20
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f1071,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(resolution,[],[f950,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f950,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(backward_demodulation,[],[f937,f945])).

fof(f937,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f423,f145])).

fof(f423,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f422,f173])).

fof(f173,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f157,f87])).

fof(f87,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f157,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f69,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f422,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f151,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f151,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f69,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f878,plain,
    ( spl8_2
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f877])).

fof(f877,plain,
    ( $false
    | spl8_2
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(resolution,[],[f876,f782])).

fof(f782,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl8_2
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f728,f766])).

fof(f766,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f765,f722])).

fof(f722,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f248,f708])).

fof(f708,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f707,f173])).

fof(f707,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f610,f674])).

fof(f674,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f195,f248])).

fof(f195,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl8_11
  <=> sK2 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f610,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl8_11 ),
    inference(superposition,[],[f81,f195])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f248,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl8_16
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f765,plain,
    ( sK0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f440,f708])).

fof(f440,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl8_22
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f728,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl8_2
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f677,f708])).

fof(f677,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl8_2
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f132,f674])).

fof(f132,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f876,plain,
    ( ! [X16] : v1_funct_2(k1_xboole_0,k1_xboole_0,X16)
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f864,f871])).

fof(f871,plain,
    ( ! [X4,X3] : k1_xboole_0 = k1_relset_1(X3,X4,k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f856,f781])).

fof(f781,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f723,f766])).

fof(f723,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f375,f708])).

fof(f375,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f373])).

fof(f856,plain,
    ( ! [X4,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X3,X4,k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(resolution,[],[f815,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f815,plain,
    ( ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f814,f708])).

fof(f814,plain,
    ( ! [X0,X1] : m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f813,f74])).

fof(f813,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f812,f766])).

fof(f812,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f687,f74])).

fof(f687,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r1_tarski(sK0,X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f612,f674])).

fof(f612,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_tarski(sK2,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f611,f375])).

fof(f611,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_relat_1(sK3),X1) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f608,f173])).

fof(f608,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_relat_1(sK3),X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_11 ),
    inference(superposition,[],[f101,f195])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f864,plain,
    ( ! [X16] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X16,k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X16) )
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(resolution,[],[f815,f121])).

fof(f121,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f706,plain,
    ( ~ spl8_11
    | ~ spl8_16
    | spl8_21 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_16
    | spl8_21 ),
    inference(subsumption_resolution,[],[f690,f73])).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f690,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_16
    | spl8_21 ),
    inference(backward_demodulation,[],[f637,f674])).

fof(f637,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_11
    | spl8_21 ),
    inference(resolution,[],[f594,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f594,plain,
    ( r2_hidden(sK6(sK2,sK0),sK2)
    | ~ spl8_11
    | spl8_21 ),
    inference(resolution,[],[f502,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f502,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl8_11
    | spl8_21 ),
    inference(backward_demodulation,[],[f436,f195])).

fof(f436,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl8_21
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f654,plain,
    ( spl8_3
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | spl8_3
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f639,f115])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f639,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl8_3
    | ~ spl8_20 ),
    inference(resolution,[],[f520,f136])).

fof(f136,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f520,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f428,f375])).

fof(f428,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f425,f173])).

fof(f425,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f159,f101])).

fof(f159,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f70,f149])).

fof(f149,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f69,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f70,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f527,plain,
    ( spl8_19
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl8_19
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f368,f521])).

fof(f521,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f443,f375])).

fof(f443,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f69,f103])).

fof(f368,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl8_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f518,plain,
    ( spl8_19
    | spl8_4 ),
    inference(avatar_split_clause,[],[f517,f139,f367])).

fof(f517,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f445,f68])).

fof(f68,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f445,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f69,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f493,plain,
    ( spl8_2
    | ~ spl8_3
    | spl8_16
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f492])).

fof(f492,plain,
    ( $false
    | spl8_2
    | ~ spl8_3
    | spl8_16
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f491,f74])).

fof(f491,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | spl8_2
    | ~ spl8_3
    | spl8_16
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f490,f466])).

fof(f466,plain,
    ( k1_xboole_0 = sK2
    | spl8_2
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f465,f132])).

fof(f465,plain,
    ( k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f458,f464])).

fof(f464,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f455,f415])).

fof(f415,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f150,f369])).

fof(f369,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f367])).

fof(f150,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f69,f103])).

fof(f455,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f135,f103])).

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f458,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f135,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f490,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | spl8_2
    | ~ spl8_3
    | spl8_16
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f489,f247])).

fof(f247,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | spl8_16 ),
    inference(avatar_component_clause,[],[f246])).

fof(f489,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ r1_tarski(sK2,k2_relat_1(sK3))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f427,f466])).

fof(f427,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(resolution,[],[f159,f92])).

fof(f485,plain,
    ( spl8_2
    | ~ spl8_3
    | spl8_10
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl8_2
    | ~ spl8_3
    | spl8_10
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f474,f73])).

fof(f474,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_2
    | ~ spl8_3
    | spl8_10
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f242,f466])).

fof(f242,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_10 ),
    inference(resolution,[],[f219,f84])).

fof(f219,plain,
    ( r2_hidden(sK6(sK2,k2_relat_1(sK3)),sK2)
    | spl8_10 ),
    inference(resolution,[],[f191,f94])).

fof(f191,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl8_10
  <=> r1_tarski(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f441,plain,
    ( ~ spl8_21
    | spl8_22
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f432,f169,f438,f434])).

fof(f169,plain,
    ( spl8_7
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f432,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f171,f92])).

fof(f171,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f417,plain,
    ( ~ spl8_19
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl8_19
    | spl8_20 ),
    inference(subsumption_resolution,[],[f415,f374])).

fof(f407,plain,
    ( ~ spl8_5
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl8_5
    | spl8_14 ),
    inference(subsumption_resolution,[],[f405,f74])).

fof(f405,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl8_5
    | spl8_14 ),
    inference(forward_demodulation,[],[f392,f117])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f392,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | ~ spl8_5
    | spl8_14 ),
    inference(backward_demodulation,[],[f225,f145])).

fof(f225,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl8_14
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f353,plain,
    ( ~ spl8_5
    | spl8_7
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | ~ spl8_5
    | spl8_7
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f330,f74])).

fof(f330,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_5
    | spl8_7
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f256,f145])).

fof(f256,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl8_7
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f170,f248])).

fof(f170,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK3))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f310,plain,
    ( spl8_7
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl8_7
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f212,f240])).

fof(f240,plain,
    ( ~ v1_xboole_0(sK0)
    | spl8_7 ),
    inference(resolution,[],[f217,f84])).

fof(f217,plain,
    ( r2_hidden(sK6(sK0,k2_relat_1(sK3)),sK0)
    | spl8_7 ),
    inference(resolution,[],[f170,f94])).

fof(f212,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl8_13
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f307,plain,
    ( spl8_12
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f293,f73])).

fof(f293,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_12
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f208,f277])).

fof(f277,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f269,f173])).

fof(f269,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl8_16 ),
    inference(trivial_inequality_removal,[],[f268])).

fof(f268,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl8_16 ),
    inference(superposition,[],[f81,f248])).

fof(f208,plain,
    ( ~ v1_xboole_0(sK3)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl8_12
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f230,plain,
    ( ~ spl8_14
    | spl8_15 ),
    inference(avatar_split_clause,[],[f221,f227,f223])).

fof(f221,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    inference(resolution,[],[f156,f92])).

fof(f156,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f69,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f213,plain,
    ( ~ spl8_12
    | spl8_13
    | spl8_4 ),
    inference(avatar_split_clause,[],[f203,f139,f210,f206])).

fof(f203,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK3)
    | spl8_4 ),
    inference(superposition,[],[f79,f162])).

fof(f162,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl8_4 ),
    inference(backward_demodulation,[],[f150,f161])).

fof(f161,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f160,f141])).

fof(f141,plain,
    ( k1_xboole_0 != sK1
    | spl8_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f160,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f152,f68])).

fof(f152,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f69,f105])).

fof(f79,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f196,plain,
    ( ~ spl8_10
    | spl8_11 ),
    inference(avatar_split_clause,[],[f185,f193,f189])).

fof(f185,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(resolution,[],[f159,f92])).

fof(f148,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f128,f67])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,
    ( ~ v1_funct_1(sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f146,plain,
    ( ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f71,f143,f139])).

fof(f71,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f137,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f72,f134,f130,f126])).

fof(f72,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:31:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (15318)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (15344)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (15319)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (15326)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (15327)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (15317)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (15327)Refutation not found, incomplete strategy% (15327)------------------------------
% 0.22/0.52  % (15327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15319)Refutation not found, incomplete strategy% (15319)------------------------------
% 0.22/0.52  % (15319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15322)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (15341)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (15321)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (15328)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (15345)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (15327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15327)Memory used [KB]: 10746
% 0.22/0.53  % (15327)Time elapsed: 0.096 s
% 0.22/0.53  % (15327)------------------------------
% 0.22/0.53  % (15327)------------------------------
% 0.22/0.53  % (15340)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (15319)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15319)Memory used [KB]: 10874
% 0.22/0.53  % (15319)Time elapsed: 0.109 s
% 0.22/0.53  % (15319)------------------------------
% 0.22/0.53  % (15319)------------------------------
% 0.22/0.53  % (15333)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (15332)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (15325)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (15323)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.54  % (15320)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.54  % (15343)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.54  % (15324)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.55  % (15330)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.55  % (15339)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.56  % (15337)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.56  % (15335)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.56  % (15342)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.56  % (15338)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.56  % (15346)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.56  % (15334)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.56  % (15331)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.56  % (15329)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.57  % (15336)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.59  % (15325)Refutation found. Thanks to Tanya!
% 1.50/0.59  % SZS status Theorem for theBenchmark
% 1.50/0.59  % SZS output start Proof for theBenchmark
% 1.50/0.59  fof(f1075,plain,(
% 1.50/0.59    $false),
% 1.50/0.59    inference(avatar_sat_refutation,[],[f137,f146,f148,f196,f213,f230,f307,f310,f353,f407,f417,f441,f485,f493,f518,f527,f654,f706,f878,f1074])).
% 1.50/0.59  fof(f1074,plain,(
% 1.50/0.59    ~spl8_4 | ~spl8_5 | ~spl8_15 | spl8_20),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f1073])).
% 1.50/0.59  fof(f1073,plain,(
% 1.50/0.59    $false | (~spl8_4 | ~spl8_5 | ~spl8_15 | spl8_20)),
% 1.50/0.59    inference(subsumption_resolution,[],[f1072,f74])).
% 1.50/0.59  fof(f74,plain,(
% 1.50/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f6])).
% 1.50/0.59  fof(f6,axiom,(
% 1.50/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.50/0.59  fof(f1072,plain,(
% 1.50/0.59    ~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) | (~spl8_4 | ~spl8_5 | ~spl8_15 | spl8_20)),
% 1.50/0.59    inference(subsumption_resolution,[],[f1071,f951])).
% 1.50/0.59  fof(f951,plain,(
% 1.50/0.59    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl8_4 | ~spl8_5 | ~spl8_15 | spl8_20)),
% 1.50/0.59    inference(backward_demodulation,[],[f938,f945])).
% 1.50/0.59  fof(f945,plain,(
% 1.50/0.59    k1_xboole_0 = sK3 | (~spl8_4 | ~spl8_15)),
% 1.50/0.59    inference(forward_demodulation,[],[f944,f116])).
% 1.50/0.59  fof(f116,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.50/0.59    inference(equality_resolution,[],[f100])).
% 1.50/0.59  fof(f100,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.50/0.59    inference(cnf_transformation,[],[f65])).
% 1.50/0.59  fof(f65,plain,(
% 1.50/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.50/0.59    inference(flattening,[],[f64])).
% 1.50/0.59  fof(f64,plain,(
% 1.50/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.50/0.59    inference(nnf_transformation,[],[f7])).
% 1.50/0.59  fof(f7,axiom,(
% 1.50/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.59  fof(f944,plain,(
% 1.50/0.59    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl8_4 | ~spl8_15)),
% 1.50/0.59    inference(forward_demodulation,[],[f229,f140])).
% 1.50/0.59  fof(f140,plain,(
% 1.50/0.59    k1_xboole_0 = sK1 | ~spl8_4),
% 1.50/0.59    inference(avatar_component_clause,[],[f139])).
% 1.50/0.59  fof(f139,plain,(
% 1.50/0.59    spl8_4 <=> k1_xboole_0 = sK1),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.50/0.59  fof(f229,plain,(
% 1.50/0.59    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl8_15),
% 1.50/0.59    inference(avatar_component_clause,[],[f227])).
% 1.50/0.59  fof(f227,plain,(
% 1.50/0.59    spl8_15 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.50/0.59  fof(f938,plain,(
% 1.50/0.59    k1_xboole_0 != k1_relat_1(sK3) | (~spl8_5 | spl8_20)),
% 1.50/0.59    inference(backward_demodulation,[],[f374,f145])).
% 1.50/0.59  fof(f145,plain,(
% 1.50/0.59    k1_xboole_0 = sK0 | ~spl8_5),
% 1.50/0.59    inference(avatar_component_clause,[],[f143])).
% 1.50/0.59  fof(f143,plain,(
% 1.50/0.59    spl8_5 <=> k1_xboole_0 = sK0),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.50/0.59  fof(f374,plain,(
% 1.50/0.59    sK0 != k1_relat_1(sK3) | spl8_20),
% 1.50/0.59    inference(avatar_component_clause,[],[f373])).
% 1.50/0.59  fof(f373,plain,(
% 1.50/0.59    spl8_20 <=> sK0 = k1_relat_1(sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.50/0.59  fof(f1071,plain,(
% 1.50/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) | (~spl8_4 | ~spl8_5 | ~spl8_15)),
% 1.50/0.59    inference(resolution,[],[f950,f92])).
% 1.50/0.59  fof(f92,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f58])).
% 1.50/0.59  fof(f58,plain,(
% 1.50/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.59    inference(flattening,[],[f57])).
% 1.50/0.59  fof(f57,plain,(
% 1.50/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.59    inference(nnf_transformation,[],[f5])).
% 1.50/0.59  fof(f5,axiom,(
% 1.50/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.59  fof(f950,plain,(
% 1.50/0.59    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl8_4 | ~spl8_5 | ~spl8_15)),
% 1.50/0.59    inference(backward_demodulation,[],[f937,f945])).
% 1.50/0.59  fof(f937,plain,(
% 1.50/0.59    r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~spl8_5),
% 1.50/0.59    inference(backward_demodulation,[],[f423,f145])).
% 1.50/0.59  fof(f423,plain,(
% 1.50/0.59    r1_tarski(k1_relat_1(sK3),sK0)),
% 1.50/0.59    inference(subsumption_resolution,[],[f422,f173])).
% 1.50/0.59  fof(f173,plain,(
% 1.50/0.59    v1_relat_1(sK3)),
% 1.50/0.59    inference(subsumption_resolution,[],[f157,f87])).
% 1.50/0.59  fof(f87,plain,(
% 1.50/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f13])).
% 1.50/0.59  fof(f13,axiom,(
% 1.50/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.50/0.59  fof(f157,plain,(
% 1.50/0.59    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.50/0.59    inference(resolution,[],[f69,f82])).
% 1.50/0.59  fof(f82,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f32])).
% 1.50/0.59  fof(f32,plain,(
% 1.50/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.59    inference(ennf_transformation,[],[f10])).
% 1.50/0.59  fof(f10,axiom,(
% 1.50/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.50/0.59  fof(f69,plain,(
% 1.50/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.59    inference(cnf_transformation,[],[f49])).
% 1.50/0.59  fof(f49,plain,(
% 1.50/0.59    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f48])).
% 1.50/0.59  fof(f48,plain,(
% 1.50/0.59    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f28,plain,(
% 1.50/0.59    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.50/0.59    inference(flattening,[],[f27])).
% 1.50/0.59  fof(f27,plain,(
% 1.50/0.59    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.50/0.59    inference(ennf_transformation,[],[f25])).
% 1.50/0.59  fof(f25,negated_conjecture,(
% 1.50/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.50/0.59    inference(negated_conjecture,[],[f24])).
% 1.50/0.59  fof(f24,conjecture,(
% 1.50/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.50/0.59  fof(f422,plain,(
% 1.50/0.59    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 1.50/0.59    inference(resolution,[],[f151,f88])).
% 1.50/0.59  fof(f88,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f56])).
% 1.50/0.59  fof(f56,plain,(
% 1.50/0.59    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.50/0.59    inference(nnf_transformation,[],[f36])).
% 1.50/0.59  fof(f36,plain,(
% 1.50/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.59    inference(ennf_transformation,[],[f11])).
% 1.50/0.59  fof(f11,axiom,(
% 1.50/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.50/0.59  fof(f151,plain,(
% 1.50/0.59    v4_relat_1(sK3,sK0)),
% 1.50/0.59    inference(resolution,[],[f69,f104])).
% 1.50/0.59  fof(f104,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f42])).
% 1.50/0.59  fof(f42,plain,(
% 1.50/0.59    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.59    inference(ennf_transformation,[],[f26])).
% 1.50/0.59  fof(f26,plain,(
% 1.50/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.50/0.59    inference(pure_predicate_removal,[],[f18])).
% 1.50/0.59  fof(f18,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.50/0.59  fof(f878,plain,(
% 1.50/0.59    spl8_2 | ~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f877])).
% 1.50/0.59  fof(f877,plain,(
% 1.50/0.59    $false | (spl8_2 | ~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(resolution,[],[f876,f782])).
% 1.50/0.59  fof(f782,plain,(
% 1.50/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl8_2 | ~spl8_11 | ~spl8_16 | ~spl8_22)),
% 1.50/0.59    inference(backward_demodulation,[],[f728,f766])).
% 1.50/0.59  fof(f766,plain,(
% 1.50/0.59    k1_xboole_0 = sK0 | (~spl8_11 | ~spl8_16 | ~spl8_22)),
% 1.50/0.59    inference(forward_demodulation,[],[f765,f722])).
% 1.50/0.59  fof(f722,plain,(
% 1.50/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl8_11 | ~spl8_16)),
% 1.50/0.59    inference(backward_demodulation,[],[f248,f708])).
% 1.50/0.59  fof(f708,plain,(
% 1.50/0.59    k1_xboole_0 = sK3 | (~spl8_11 | ~spl8_16)),
% 1.50/0.59    inference(subsumption_resolution,[],[f707,f173])).
% 1.50/0.59  fof(f707,plain,(
% 1.50/0.59    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | (~spl8_11 | ~spl8_16)),
% 1.50/0.59    inference(subsumption_resolution,[],[f610,f674])).
% 1.50/0.59  fof(f674,plain,(
% 1.50/0.59    k1_xboole_0 = sK2 | (~spl8_11 | ~spl8_16)),
% 1.50/0.59    inference(backward_demodulation,[],[f195,f248])).
% 1.50/0.59  fof(f195,plain,(
% 1.50/0.59    sK2 = k2_relat_1(sK3) | ~spl8_11),
% 1.50/0.59    inference(avatar_component_clause,[],[f193])).
% 1.50/0.59  fof(f193,plain,(
% 1.50/0.59    spl8_11 <=> sK2 = k2_relat_1(sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.50/0.59  fof(f610,plain,(
% 1.50/0.59    k1_xboole_0 != sK2 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl8_11),
% 1.50/0.59    inference(superposition,[],[f81,f195])).
% 1.50/0.59  fof(f81,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f31])).
% 1.50/0.59  fof(f31,plain,(
% 1.50/0.59    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.59    inference(flattening,[],[f30])).
% 1.50/0.59  fof(f30,plain,(
% 1.50/0.59    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.59    inference(ennf_transformation,[],[f15])).
% 1.50/0.59  fof(f15,axiom,(
% 1.50/0.59    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.50/0.59  fof(f248,plain,(
% 1.50/0.59    k1_xboole_0 = k2_relat_1(sK3) | ~spl8_16),
% 1.50/0.59    inference(avatar_component_clause,[],[f246])).
% 1.50/0.59  fof(f246,plain,(
% 1.50/0.59    spl8_16 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.50/0.59  fof(f765,plain,(
% 1.50/0.59    sK0 = k2_relat_1(k1_xboole_0) | (~spl8_11 | ~spl8_16 | ~spl8_22)),
% 1.50/0.59    inference(forward_demodulation,[],[f440,f708])).
% 1.50/0.59  fof(f440,plain,(
% 1.50/0.59    sK0 = k2_relat_1(sK3) | ~spl8_22),
% 1.50/0.59    inference(avatar_component_clause,[],[f438])).
% 1.50/0.59  fof(f438,plain,(
% 1.50/0.59    spl8_22 <=> sK0 = k2_relat_1(sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.50/0.59  fof(f728,plain,(
% 1.50/0.59    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl8_2 | ~spl8_11 | ~spl8_16)),
% 1.50/0.59    inference(backward_demodulation,[],[f677,f708])).
% 1.50/0.59  fof(f677,plain,(
% 1.50/0.59    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl8_2 | ~spl8_11 | ~spl8_16)),
% 1.50/0.59    inference(backward_demodulation,[],[f132,f674])).
% 1.50/0.59  fof(f132,plain,(
% 1.50/0.59    ~v1_funct_2(sK3,sK0,sK2) | spl8_2),
% 1.50/0.59    inference(avatar_component_clause,[],[f130])).
% 1.50/0.59  fof(f130,plain,(
% 1.50/0.59    spl8_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.50/0.59  fof(f876,plain,(
% 1.50/0.59    ( ! [X16] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X16)) ) | (~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(subsumption_resolution,[],[f864,f871])).
% 1.50/0.59  fof(f871,plain,(
% 1.50/0.59    ( ! [X4,X3] : (k1_xboole_0 = k1_relset_1(X3,X4,k1_xboole_0)) ) | (~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(forward_demodulation,[],[f856,f781])).
% 1.50/0.59  fof(f781,plain,(
% 1.50/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(backward_demodulation,[],[f723,f766])).
% 1.50/0.59  fof(f723,plain,(
% 1.50/0.59    sK0 = k1_relat_1(k1_xboole_0) | (~spl8_11 | ~spl8_16 | ~spl8_20)),
% 1.50/0.59    inference(backward_demodulation,[],[f375,f708])).
% 1.50/0.59  fof(f375,plain,(
% 1.50/0.59    sK0 = k1_relat_1(sK3) | ~spl8_20),
% 1.50/0.59    inference(avatar_component_clause,[],[f373])).
% 1.50/0.59  fof(f856,plain,(
% 1.50/0.59    ( ! [X4,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X3,X4,k1_xboole_0)) ) | (~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(resolution,[],[f815,f103])).
% 1.50/0.59  fof(f103,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f41])).
% 1.50/0.59  fof(f41,plain,(
% 1.50/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.59    inference(ennf_transformation,[],[f19])).
% 1.50/0.59  fof(f19,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.50/0.59  fof(f815,plain,(
% 1.50/0.59    ( ! [X0,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(forward_demodulation,[],[f814,f708])).
% 1.50/0.59  fof(f814,plain,(
% 1.50/0.59    ( ! [X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(subsumption_resolution,[],[f813,f74])).
% 1.50/0.59  fof(f813,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(forward_demodulation,[],[f812,f766])).
% 1.50/0.59  fof(f812,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl8_11 | ~spl8_16 | ~spl8_20)),
% 1.50/0.59    inference(subsumption_resolution,[],[f687,f74])).
% 1.50/0.59  fof(f687,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~r1_tarski(sK0,X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl8_11 | ~spl8_16 | ~spl8_20)),
% 1.50/0.59    inference(backward_demodulation,[],[f612,f674])).
% 1.50/0.59  fof(f612,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(sK2,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl8_11 | ~spl8_20)),
% 1.50/0.59    inference(forward_demodulation,[],[f611,f375])).
% 1.50/0.59  fof(f611,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(sK3),X1)) ) | ~spl8_11),
% 1.50/0.59    inference(subsumption_resolution,[],[f608,f173])).
% 1.50/0.59  fof(f608,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(sK3),X1) | ~v1_relat_1(sK3)) ) | ~spl8_11),
% 1.50/0.59    inference(superposition,[],[f101,f195])).
% 1.50/0.59  fof(f101,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f39])).
% 1.50/0.59  fof(f39,plain,(
% 1.50/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.50/0.59    inference(flattening,[],[f38])).
% 1.50/0.59  fof(f38,plain,(
% 1.50/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.50/0.59    inference(ennf_transformation,[],[f21])).
% 1.50/0.59  fof(f21,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.50/0.59  fof(f864,plain,(
% 1.50/0.59    ( ! [X16] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X16,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X16)) ) | (~spl8_11 | ~spl8_16 | ~spl8_20 | ~spl8_22)),
% 1.50/0.59    inference(resolution,[],[f815,f121])).
% 1.50/0.59  fof(f121,plain,(
% 1.50/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.50/0.59    inference(equality_resolution,[],[f108])).
% 1.50/0.59  fof(f108,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f66])).
% 1.50/0.59  fof(f66,plain,(
% 1.50/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.59    inference(nnf_transformation,[],[f44])).
% 1.50/0.59  fof(f44,plain,(
% 1.50/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.59    inference(flattening,[],[f43])).
% 1.50/0.59  fof(f43,plain,(
% 1.50/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.59    inference(ennf_transformation,[],[f23])).
% 1.50/0.59  fof(f23,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.50/0.59  fof(f706,plain,(
% 1.50/0.59    ~spl8_11 | ~spl8_16 | spl8_21),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f705])).
% 1.50/0.59  fof(f705,plain,(
% 1.50/0.59    $false | (~spl8_11 | ~spl8_16 | spl8_21)),
% 1.50/0.59    inference(subsumption_resolution,[],[f690,f73])).
% 1.50/0.59  fof(f73,plain,(
% 1.50/0.59    v1_xboole_0(k1_xboole_0)),
% 1.50/0.59    inference(cnf_transformation,[],[f3])).
% 1.50/0.59  fof(f3,axiom,(
% 1.50/0.59    v1_xboole_0(k1_xboole_0)),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.50/0.59  fof(f690,plain,(
% 1.50/0.59    ~v1_xboole_0(k1_xboole_0) | (~spl8_11 | ~spl8_16 | spl8_21)),
% 1.50/0.59    inference(backward_demodulation,[],[f637,f674])).
% 1.50/0.59  fof(f637,plain,(
% 1.50/0.59    ~v1_xboole_0(sK2) | (~spl8_11 | spl8_21)),
% 1.50/0.59    inference(resolution,[],[f594,f84])).
% 1.50/0.59  fof(f84,plain,(
% 1.50/0.59    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f53])).
% 1.50/0.59  fof(f53,plain,(
% 1.50/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 1.50/0.59  fof(f52,plain,(
% 1.50/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f51,plain,(
% 1.50/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.50/0.59    inference(rectify,[],[f50])).
% 1.50/0.59  fof(f50,plain,(
% 1.50/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.50/0.59    inference(nnf_transformation,[],[f1])).
% 1.50/0.59  fof(f1,axiom,(
% 1.50/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.50/0.59  fof(f594,plain,(
% 1.50/0.59    r2_hidden(sK6(sK2,sK0),sK2) | (~spl8_11 | spl8_21)),
% 1.50/0.59    inference(resolution,[],[f502,f94])).
% 1.50/0.59  fof(f94,plain,(
% 1.50/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f62])).
% 1.50/0.59  fof(f62,plain,(
% 1.50/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f60,f61])).
% 1.50/0.59  fof(f61,plain,(
% 1.50/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f60,plain,(
% 1.50/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.59    inference(rectify,[],[f59])).
% 1.50/0.59  fof(f59,plain,(
% 1.50/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.59    inference(nnf_transformation,[],[f37])).
% 1.50/0.59  fof(f37,plain,(
% 1.50/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.59    inference(ennf_transformation,[],[f2])).
% 1.50/0.59  fof(f2,axiom,(
% 1.50/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.59  fof(f502,plain,(
% 1.50/0.59    ~r1_tarski(sK2,sK0) | (~spl8_11 | spl8_21)),
% 1.50/0.59    inference(backward_demodulation,[],[f436,f195])).
% 1.50/0.59  fof(f436,plain,(
% 1.50/0.59    ~r1_tarski(k2_relat_1(sK3),sK0) | spl8_21),
% 1.50/0.59    inference(avatar_component_clause,[],[f434])).
% 1.50/0.59  fof(f434,plain,(
% 1.50/0.59    spl8_21 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.50/0.59  fof(f654,plain,(
% 1.50/0.59    spl8_3 | ~spl8_20),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f653])).
% 1.50/0.59  fof(f653,plain,(
% 1.50/0.59    $false | (spl8_3 | ~spl8_20)),
% 1.50/0.59    inference(subsumption_resolution,[],[f639,f115])).
% 1.50/0.59  fof(f115,plain,(
% 1.50/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.59    inference(equality_resolution,[],[f90])).
% 1.50/0.59  fof(f90,plain,(
% 1.50/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.50/0.59    inference(cnf_transformation,[],[f58])).
% 1.50/0.59  fof(f639,plain,(
% 1.50/0.59    ~r1_tarski(sK0,sK0) | (spl8_3 | ~spl8_20)),
% 1.50/0.59    inference(resolution,[],[f520,f136])).
% 1.50/0.59  fof(f136,plain,(
% 1.50/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl8_3),
% 1.50/0.59    inference(avatar_component_clause,[],[f134])).
% 1.50/0.59  fof(f134,plain,(
% 1.50/0.59    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.50/0.59  fof(f520,plain,(
% 1.50/0.59    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(sK0,X0)) ) | ~spl8_20),
% 1.50/0.59    inference(backward_demodulation,[],[f428,f375])).
% 1.50/0.59  fof(f428,plain,(
% 1.50/0.59    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0)) )),
% 1.50/0.59    inference(subsumption_resolution,[],[f425,f173])).
% 1.50/0.59  fof(f425,plain,(
% 1.50/0.59    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 1.50/0.59    inference(resolution,[],[f159,f101])).
% 1.50/0.59  fof(f159,plain,(
% 1.50/0.59    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.50/0.59    inference(backward_demodulation,[],[f70,f149])).
% 1.50/0.59  fof(f149,plain,(
% 1.50/0.59    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.50/0.59    inference(resolution,[],[f69,f102])).
% 1.50/0.59  fof(f102,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f40])).
% 1.50/0.59  fof(f40,plain,(
% 1.50/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.59    inference(ennf_transformation,[],[f20])).
% 1.50/0.59  fof(f20,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.50/0.59  fof(f70,plain,(
% 1.50/0.59    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.50/0.59    inference(cnf_transformation,[],[f49])).
% 1.50/0.59  fof(f527,plain,(
% 1.50/0.59    spl8_19 | ~spl8_20),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f526])).
% 1.50/0.59  fof(f526,plain,(
% 1.50/0.59    $false | (spl8_19 | ~spl8_20)),
% 1.50/0.59    inference(subsumption_resolution,[],[f368,f521])).
% 1.50/0.59  fof(f521,plain,(
% 1.50/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_20),
% 1.50/0.59    inference(backward_demodulation,[],[f443,f375])).
% 1.50/0.59  fof(f443,plain,(
% 1.50/0.59    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.50/0.59    inference(resolution,[],[f69,f103])).
% 1.50/0.59  fof(f368,plain,(
% 1.50/0.59    sK0 != k1_relset_1(sK0,sK1,sK3) | spl8_19),
% 1.50/0.59    inference(avatar_component_clause,[],[f367])).
% 1.50/0.59  fof(f367,plain,(
% 1.50/0.59    spl8_19 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.50/0.59  fof(f518,plain,(
% 1.50/0.59    spl8_19 | spl8_4),
% 1.50/0.59    inference(avatar_split_clause,[],[f517,f139,f367])).
% 1.50/0.59  fof(f517,plain,(
% 1.50/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.50/0.59    inference(subsumption_resolution,[],[f445,f68])).
% 1.50/0.59  fof(f68,plain,(
% 1.50/0.59    v1_funct_2(sK3,sK0,sK1)),
% 1.50/0.59    inference(cnf_transformation,[],[f49])).
% 1.50/0.59  fof(f445,plain,(
% 1.50/0.59    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.50/0.59    inference(resolution,[],[f69,f105])).
% 1.50/0.59  fof(f105,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.50/0.59    inference(cnf_transformation,[],[f66])).
% 1.50/0.59  fof(f493,plain,(
% 1.50/0.59    spl8_2 | ~spl8_3 | spl8_16 | ~spl8_19),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f492])).
% 1.50/0.59  fof(f492,plain,(
% 1.50/0.59    $false | (spl8_2 | ~spl8_3 | spl8_16 | ~spl8_19)),
% 1.50/0.59    inference(subsumption_resolution,[],[f491,f74])).
% 1.50/0.59  fof(f491,plain,(
% 1.50/0.59    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | (spl8_2 | ~spl8_3 | spl8_16 | ~spl8_19)),
% 1.50/0.59    inference(forward_demodulation,[],[f490,f466])).
% 1.50/0.59  fof(f466,plain,(
% 1.50/0.59    k1_xboole_0 = sK2 | (spl8_2 | ~spl8_3 | ~spl8_19)),
% 1.50/0.59    inference(subsumption_resolution,[],[f465,f132])).
% 1.50/0.59  fof(f465,plain,(
% 1.50/0.59    k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | (~spl8_3 | ~spl8_19)),
% 1.50/0.59    inference(subsumption_resolution,[],[f458,f464])).
% 1.50/0.59  fof(f464,plain,(
% 1.50/0.59    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl8_3 | ~spl8_19)),
% 1.50/0.59    inference(forward_demodulation,[],[f455,f415])).
% 1.50/0.59  fof(f415,plain,(
% 1.50/0.59    sK0 = k1_relat_1(sK3) | ~spl8_19),
% 1.50/0.59    inference(backward_demodulation,[],[f150,f369])).
% 1.50/0.59  fof(f369,plain,(
% 1.50/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_19),
% 1.50/0.59    inference(avatar_component_clause,[],[f367])).
% 1.50/0.59  fof(f150,plain,(
% 1.50/0.59    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.50/0.59    inference(resolution,[],[f69,f103])).
% 1.50/0.59  fof(f455,plain,(
% 1.50/0.59    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl8_3),
% 1.50/0.59    inference(resolution,[],[f135,f103])).
% 1.50/0.59  fof(f135,plain,(
% 1.50/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl8_3),
% 1.50/0.59    inference(avatar_component_clause,[],[f134])).
% 1.50/0.59  fof(f458,plain,(
% 1.50/0.59    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | ~spl8_3),
% 1.50/0.59    inference(resolution,[],[f135,f107])).
% 1.50/0.59  fof(f107,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f66])).
% 1.50/0.59  fof(f490,plain,(
% 1.50/0.59    ~r1_tarski(sK2,k2_relat_1(sK3)) | (spl8_2 | ~spl8_3 | spl8_16 | ~spl8_19)),
% 1.50/0.59    inference(subsumption_resolution,[],[f489,f247])).
% 1.50/0.59  fof(f247,plain,(
% 1.50/0.59    k1_xboole_0 != k2_relat_1(sK3) | spl8_16),
% 1.50/0.59    inference(avatar_component_clause,[],[f246])).
% 1.50/0.59  fof(f489,plain,(
% 1.50/0.59    k1_xboole_0 = k2_relat_1(sK3) | ~r1_tarski(sK2,k2_relat_1(sK3)) | (spl8_2 | ~spl8_3 | ~spl8_19)),
% 1.50/0.59    inference(forward_demodulation,[],[f427,f466])).
% 1.50/0.59  fof(f427,plain,(
% 1.50/0.59    sK2 = k2_relat_1(sK3) | ~r1_tarski(sK2,k2_relat_1(sK3))),
% 1.50/0.59    inference(resolution,[],[f159,f92])).
% 1.50/0.59  fof(f485,plain,(
% 1.50/0.59    spl8_2 | ~spl8_3 | spl8_10 | ~spl8_19),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f484])).
% 1.50/0.59  fof(f484,plain,(
% 1.50/0.59    $false | (spl8_2 | ~spl8_3 | spl8_10 | ~spl8_19)),
% 1.50/0.59    inference(subsumption_resolution,[],[f474,f73])).
% 1.50/0.59  fof(f474,plain,(
% 1.50/0.59    ~v1_xboole_0(k1_xboole_0) | (spl8_2 | ~spl8_3 | spl8_10 | ~spl8_19)),
% 1.50/0.59    inference(backward_demodulation,[],[f242,f466])).
% 1.50/0.59  fof(f242,plain,(
% 1.50/0.59    ~v1_xboole_0(sK2) | spl8_10),
% 1.50/0.59    inference(resolution,[],[f219,f84])).
% 1.50/0.59  fof(f219,plain,(
% 1.50/0.59    r2_hidden(sK6(sK2,k2_relat_1(sK3)),sK2) | spl8_10),
% 1.50/0.59    inference(resolution,[],[f191,f94])).
% 1.50/0.59  fof(f191,plain,(
% 1.50/0.59    ~r1_tarski(sK2,k2_relat_1(sK3)) | spl8_10),
% 1.50/0.59    inference(avatar_component_clause,[],[f189])).
% 1.50/0.59  fof(f189,plain,(
% 1.50/0.59    spl8_10 <=> r1_tarski(sK2,k2_relat_1(sK3))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.50/0.59  fof(f441,plain,(
% 1.50/0.59    ~spl8_21 | spl8_22 | ~spl8_7),
% 1.50/0.59    inference(avatar_split_clause,[],[f432,f169,f438,f434])).
% 1.50/0.59  fof(f169,plain,(
% 1.50/0.59    spl8_7 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.50/0.59  fof(f432,plain,(
% 1.50/0.59    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0) | ~spl8_7),
% 1.50/0.59    inference(resolution,[],[f171,f92])).
% 1.50/0.59  fof(f171,plain,(
% 1.50/0.59    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl8_7),
% 1.50/0.59    inference(avatar_component_clause,[],[f169])).
% 1.50/0.59  fof(f417,plain,(
% 1.50/0.59    ~spl8_19 | spl8_20),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f416])).
% 1.50/0.59  fof(f416,plain,(
% 1.50/0.59    $false | (~spl8_19 | spl8_20)),
% 1.50/0.59    inference(subsumption_resolution,[],[f415,f374])).
% 1.50/0.59  fof(f407,plain,(
% 1.50/0.59    ~spl8_5 | spl8_14),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f406])).
% 1.50/0.59  fof(f406,plain,(
% 1.50/0.59    $false | (~spl8_5 | spl8_14)),
% 1.50/0.59    inference(subsumption_resolution,[],[f405,f74])).
% 1.50/0.59  fof(f405,plain,(
% 1.50/0.59    ~r1_tarski(k1_xboole_0,sK3) | (~spl8_5 | spl8_14)),
% 1.50/0.59    inference(forward_demodulation,[],[f392,f117])).
% 1.50/0.59  fof(f117,plain,(
% 1.50/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.50/0.59    inference(equality_resolution,[],[f99])).
% 1.50/0.59  fof(f99,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.50/0.59    inference(cnf_transformation,[],[f65])).
% 1.50/0.59  fof(f392,plain,(
% 1.50/0.59    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | (~spl8_5 | spl8_14)),
% 1.50/0.59    inference(backward_demodulation,[],[f225,f145])).
% 1.50/0.59  fof(f225,plain,(
% 1.50/0.59    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl8_14),
% 1.50/0.59    inference(avatar_component_clause,[],[f223])).
% 1.50/0.59  fof(f223,plain,(
% 1.50/0.59    spl8_14 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.50/0.59  fof(f353,plain,(
% 1.50/0.59    ~spl8_5 | spl8_7 | ~spl8_16),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f352])).
% 1.50/0.59  fof(f352,plain,(
% 1.50/0.59    $false | (~spl8_5 | spl8_7 | ~spl8_16)),
% 1.50/0.59    inference(subsumption_resolution,[],[f330,f74])).
% 1.50/0.59  fof(f330,plain,(
% 1.50/0.59    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl8_5 | spl8_7 | ~spl8_16)),
% 1.50/0.59    inference(backward_demodulation,[],[f256,f145])).
% 1.50/0.59  fof(f256,plain,(
% 1.50/0.59    ~r1_tarski(sK0,k1_xboole_0) | (spl8_7 | ~spl8_16)),
% 1.50/0.59    inference(backward_demodulation,[],[f170,f248])).
% 1.50/0.59  fof(f170,plain,(
% 1.50/0.59    ~r1_tarski(sK0,k2_relat_1(sK3)) | spl8_7),
% 1.50/0.59    inference(avatar_component_clause,[],[f169])).
% 1.50/0.59  fof(f310,plain,(
% 1.50/0.59    spl8_7 | ~spl8_13),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f309])).
% 1.50/0.59  fof(f309,plain,(
% 1.50/0.59    $false | (spl8_7 | ~spl8_13)),
% 1.50/0.59    inference(subsumption_resolution,[],[f212,f240])).
% 1.50/0.59  fof(f240,plain,(
% 1.50/0.59    ~v1_xboole_0(sK0) | spl8_7),
% 1.50/0.59    inference(resolution,[],[f217,f84])).
% 1.50/0.59  fof(f217,plain,(
% 1.50/0.59    r2_hidden(sK6(sK0,k2_relat_1(sK3)),sK0) | spl8_7),
% 1.50/0.59    inference(resolution,[],[f170,f94])).
% 1.50/0.59  fof(f212,plain,(
% 1.50/0.59    v1_xboole_0(sK0) | ~spl8_13),
% 1.50/0.59    inference(avatar_component_clause,[],[f210])).
% 1.50/0.59  fof(f210,plain,(
% 1.50/0.59    spl8_13 <=> v1_xboole_0(sK0)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.50/0.59  fof(f307,plain,(
% 1.50/0.59    spl8_12 | ~spl8_16),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f306])).
% 1.50/0.59  fof(f306,plain,(
% 1.50/0.59    $false | (spl8_12 | ~spl8_16)),
% 1.50/0.59    inference(subsumption_resolution,[],[f293,f73])).
% 1.50/0.59  fof(f293,plain,(
% 1.50/0.59    ~v1_xboole_0(k1_xboole_0) | (spl8_12 | ~spl8_16)),
% 1.50/0.59    inference(backward_demodulation,[],[f208,f277])).
% 1.50/0.59  fof(f277,plain,(
% 1.50/0.59    k1_xboole_0 = sK3 | ~spl8_16),
% 1.50/0.59    inference(subsumption_resolution,[],[f269,f173])).
% 1.50/0.59  fof(f269,plain,(
% 1.50/0.59    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl8_16),
% 1.50/0.59    inference(trivial_inequality_removal,[],[f268])).
% 1.50/0.59  fof(f268,plain,(
% 1.50/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl8_16),
% 1.50/0.59    inference(superposition,[],[f81,f248])).
% 1.50/0.59  fof(f208,plain,(
% 1.50/0.59    ~v1_xboole_0(sK3) | spl8_12),
% 1.50/0.59    inference(avatar_component_clause,[],[f206])).
% 1.50/0.59  fof(f206,plain,(
% 1.50/0.59    spl8_12 <=> v1_xboole_0(sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.50/0.59  fof(f230,plain,(
% 1.50/0.59    ~spl8_14 | spl8_15),
% 1.50/0.59    inference(avatar_split_clause,[],[f221,f227,f223])).
% 1.50/0.59  fof(f221,plain,(
% 1.50/0.59    sK3 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.50/0.59    inference(resolution,[],[f156,f92])).
% 1.50/0.59  fof(f156,plain,(
% 1.50/0.59    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.50/0.59    inference(resolution,[],[f69,f96])).
% 1.50/0.59  fof(f96,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f63])).
% 1.50/0.59  fof(f63,plain,(
% 1.50/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.50/0.59    inference(nnf_transformation,[],[f8])).
% 1.50/0.59  fof(f8,axiom,(
% 1.50/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.50/0.59  fof(f213,plain,(
% 1.50/0.59    ~spl8_12 | spl8_13 | spl8_4),
% 1.50/0.59    inference(avatar_split_clause,[],[f203,f139,f210,f206])).
% 1.50/0.59  fof(f203,plain,(
% 1.50/0.59    v1_xboole_0(sK0) | ~v1_xboole_0(sK3) | spl8_4),
% 1.50/0.59    inference(superposition,[],[f79,f162])).
% 1.50/0.59  fof(f162,plain,(
% 1.50/0.59    sK0 = k1_relat_1(sK3) | spl8_4),
% 1.50/0.59    inference(backward_demodulation,[],[f150,f161])).
% 1.50/0.59  fof(f161,plain,(
% 1.50/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | spl8_4),
% 1.50/0.59    inference(subsumption_resolution,[],[f160,f141])).
% 1.50/0.59  fof(f141,plain,(
% 1.50/0.59    k1_xboole_0 != sK1 | spl8_4),
% 1.50/0.59    inference(avatar_component_clause,[],[f139])).
% 1.50/0.59  fof(f160,plain,(
% 1.50/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.50/0.59    inference(subsumption_resolution,[],[f152,f68])).
% 1.50/0.59  fof(f152,plain,(
% 1.50/0.59    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.50/0.59    inference(resolution,[],[f69,f105])).
% 1.50/0.59  fof(f79,plain,(
% 1.50/0.59    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f29])).
% 1.50/0.59  fof(f29,plain,(
% 1.50/0.59    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.50/0.59    inference(ennf_transformation,[],[f12])).
% 1.50/0.59  fof(f12,axiom,(
% 1.50/0.59    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.50/0.59  fof(f196,plain,(
% 1.50/0.59    ~spl8_10 | spl8_11),
% 1.50/0.59    inference(avatar_split_clause,[],[f185,f193,f189])).
% 1.50/0.59  fof(f185,plain,(
% 1.50/0.59    sK2 = k2_relat_1(sK3) | ~r1_tarski(sK2,k2_relat_1(sK3))),
% 1.50/0.59    inference(resolution,[],[f159,f92])).
% 1.50/0.59  fof(f148,plain,(
% 1.50/0.59    spl8_1),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f147])).
% 1.50/0.59  fof(f147,plain,(
% 1.50/0.59    $false | spl8_1),
% 1.50/0.59    inference(subsumption_resolution,[],[f128,f67])).
% 1.50/0.59  fof(f67,plain,(
% 1.50/0.59    v1_funct_1(sK3)),
% 1.50/0.59    inference(cnf_transformation,[],[f49])).
% 1.50/0.59  fof(f128,plain,(
% 1.50/0.59    ~v1_funct_1(sK3) | spl8_1),
% 1.50/0.59    inference(avatar_component_clause,[],[f126])).
% 1.50/0.59  fof(f126,plain,(
% 1.50/0.59    spl8_1 <=> v1_funct_1(sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.50/0.59  fof(f146,plain,(
% 1.50/0.59    ~spl8_4 | spl8_5),
% 1.50/0.59    inference(avatar_split_clause,[],[f71,f143,f139])).
% 1.50/0.59  fof(f71,plain,(
% 1.50/0.59    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.50/0.59    inference(cnf_transformation,[],[f49])).
% 1.50/0.59  fof(f137,plain,(
% 1.50/0.59    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.50/0.59    inference(avatar_split_clause,[],[f72,f134,f130,f126])).
% 1.50/0.59  fof(f72,plain,(
% 1.50/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 1.50/0.59    inference(cnf_transformation,[],[f49])).
% 1.50/0.59  % SZS output end Proof for theBenchmark
% 1.50/0.59  % (15325)------------------------------
% 1.50/0.59  % (15325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.59  % (15325)Termination reason: Refutation
% 1.50/0.59  
% 1.50/0.59  % (15325)Memory used [KB]: 11001
% 1.50/0.59  % (15325)Time elapsed: 0.167 s
% 1.50/0.59  % (15325)------------------------------
% 1.50/0.59  % (15325)------------------------------
% 1.50/0.59  % (15316)Success in time 0.222 s
%------------------------------------------------------------------------------
