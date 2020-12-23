%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 612 expanded)
%              Number of leaves         :   19 ( 159 expanded)
%              Depth                    :   17
%              Number of atoms          :  469 (3057 expanded)
%              Number of equality atoms :  134 ( 960 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f90,f92,f105,f139,f162,f307,f320,f336,f483])).

fof(f483,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f481,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f481,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f471,f88])).

fof(f88,plain,
    ( k1_xboole_0 != sK0
    | spl4_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f471,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f419,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f419,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f383,f399])).

fof(f399,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f367,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f367,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f366,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f366,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f159,f100])).

fof(f100,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f159,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f79,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f383,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f76,f100])).

fof(f76,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f336,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f334,f332])).

fof(f332,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f278,f44])).

fof(f278,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f211,f67])).

fof(f67,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f211,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f173,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(resolution,[],[f183,f43])).

fof(f183,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f178,f61])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f178,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f111,f89])).

fof(f89,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f111,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f36,f45])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f26])).

fof(f26,plain,
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f173,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f76,f89])).

fof(f334,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f333,f89])).

fof(f333,plain,
    ( sK0 = k1_relset_1(sK0,sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f103,f191])).

fof(f103,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_7
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f320,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f318,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f318,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f317,f304])).

fof(f304,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f218,f303])).

fof(f303,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f291,f44])).

fof(f291,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f219,f68])).

fof(f68,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f219,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f187,f191])).

fof(f187,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f171,f84])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f171,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f35,f89])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f218,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f186,f191])).

fof(f186,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f176,f84])).

fof(f176,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f107,f89])).

fof(f107,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f317,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f316,f191])).

fof(f316,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f136,f89])).

fof(f136,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f135,f106])).

fof(f106,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f36,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f135,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f133,f113])).

fof(f113,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f37,f110])).

fof(f110,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f37,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f133,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f80,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f307,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(subsumption_resolution,[],[f305,f212])).

fof(f212,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl4_5
    | spl4_7 ),
    inference(backward_demodulation,[],[f175,f191])).

fof(f175,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl4_5
    | spl4_7 ),
    inference(backward_demodulation,[],[f104,f89])).

fof(f104,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f305,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f213,f304])).

fof(f213,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f180,f191])).

fof(f180,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f155,f89])).

fof(f155,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f79,f58])).

fof(f162,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl4_3
    | spl4_4
    | spl4_7 ),
    inference(subsumption_resolution,[],[f160,f104])).

fof(f160,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_3
    | spl4_4 ),
    inference(forward_demodulation,[],[f155,f112])).

fof(f112,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(forward_demodulation,[],[f107,f95])).

fof(f95,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f94,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f93,f85])).

fof(f85,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f93,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f139,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f137,f63])).

fof(f137,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_3
    | spl4_4 ),
    inference(forward_demodulation,[],[f136,f112])).

fof(f105,plain,
    ( ~ spl4_3
    | spl4_6
    | ~ spl4_7
    | spl4_2 ),
    inference(avatar_split_clause,[],[f96,f74,f102,f98,f78])).

fof(f96,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_2 ),
    inference(resolution,[],[f76,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f72,f34])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f90,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f38,f87,f83])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f39,f78,f74,f70])).

fof(f39,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:35:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.49  % (18780)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (18787)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.50  % (18796)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (18779)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (18791)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (18795)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (18773)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (18781)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (18772)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (18771)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (18777)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (18772)Refutation not found, incomplete strategy% (18772)------------------------------
% 0.20/0.52  % (18772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18772)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18772)Memory used [KB]: 10618
% 0.20/0.52  % (18772)Time elapsed: 0.109 s
% 0.20/0.52  % (18772)------------------------------
% 0.20/0.52  % (18772)------------------------------
% 0.20/0.52  % (18792)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (18790)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (18778)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (18789)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (18774)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (18776)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (18786)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (18783)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (18782)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (18775)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (18785)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (18788)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (18782)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (18794)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.44/0.54  % SZS output start Proof for theBenchmark
% 1.44/0.54  fof(f487,plain,(
% 1.44/0.54    $false),
% 1.44/0.54    inference(avatar_sat_refutation,[],[f81,f90,f92,f105,f139,f162,f307,f320,f336,f483])).
% 1.44/0.54  fof(f483,plain,(
% 1.44/0.54    spl4_2 | ~spl4_3 | spl4_5 | ~spl4_6),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f482])).
% 1.44/0.54  fof(f482,plain,(
% 1.44/0.54    $false | (spl4_2 | ~spl4_3 | spl4_5 | ~spl4_6)),
% 1.44/0.54    inference(subsumption_resolution,[],[f481,f44])).
% 1.44/0.54  fof(f44,plain,(
% 1.44/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f4])).
% 1.44/0.54  fof(f4,axiom,(
% 1.44/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.44/0.54  fof(f481,plain,(
% 1.44/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl4_2 | ~spl4_3 | spl4_5 | ~spl4_6)),
% 1.44/0.54    inference(subsumption_resolution,[],[f471,f88])).
% 1.44/0.54  fof(f88,plain,(
% 1.44/0.54    k1_xboole_0 != sK0 | spl4_5),
% 1.44/0.54    inference(avatar_component_clause,[],[f87])).
% 1.44/0.54  fof(f87,plain,(
% 1.44/0.54    spl4_5 <=> k1_xboole_0 = sK0),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.44/0.54  fof(f471,plain,(
% 1.44/0.54    k1_xboole_0 = sK0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl4_2 | ~spl4_3 | ~spl4_6)),
% 1.44/0.54    inference(resolution,[],[f419,f65])).
% 1.44/0.54  fof(f65,plain,(
% 1.44/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.44/0.54    inference(equality_resolution,[],[f64])).
% 1.44/0.54  fof(f64,plain,(
% 1.44/0.54    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(equality_resolution,[],[f56])).
% 1.44/0.54  fof(f56,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f33])).
% 1.44/0.54  fof(f33,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(nnf_transformation,[],[f21])).
% 1.44/0.54  fof(f21,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(flattening,[],[f20])).
% 1.44/0.54  fof(f20,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f13])).
% 1.44/0.54  fof(f13,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.44/0.54  fof(f419,plain,(
% 1.44/0.54    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_2 | ~spl4_3 | ~spl4_6)),
% 1.44/0.54    inference(backward_demodulation,[],[f383,f399])).
% 1.44/0.54  fof(f399,plain,(
% 1.44/0.54    k1_xboole_0 = sK3 | (~spl4_3 | ~spl4_6)),
% 1.44/0.54    inference(resolution,[],[f367,f43])).
% 1.44/0.54  fof(f43,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f18])).
% 1.44/0.54  fof(f18,plain,(
% 1.44/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.44/0.54    inference(ennf_transformation,[],[f2])).
% 1.44/0.54  fof(f2,axiom,(
% 1.44/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.44/0.54  fof(f367,plain,(
% 1.44/0.54    r1_tarski(sK3,k1_xboole_0) | (~spl4_3 | ~spl4_6)),
% 1.44/0.54    inference(forward_demodulation,[],[f366,f60])).
% 1.44/0.54  fof(f60,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.44/0.54    inference(equality_resolution,[],[f42])).
% 1.44/0.54  fof(f42,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.44/0.54    inference(cnf_transformation,[],[f29])).
% 1.44/0.54  fof(f29,plain,(
% 1.44/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.44/0.54    inference(flattening,[],[f28])).
% 1.44/0.54  fof(f28,plain,(
% 1.44/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.44/0.54    inference(nnf_transformation,[],[f3])).
% 1.44/0.54  fof(f3,axiom,(
% 1.44/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.44/0.54  fof(f366,plain,(
% 1.44/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl4_3 | ~spl4_6)),
% 1.44/0.54    inference(forward_demodulation,[],[f159,f100])).
% 1.44/0.54  fof(f100,plain,(
% 1.44/0.54    k1_xboole_0 = sK2 | ~spl4_6),
% 1.44/0.54    inference(avatar_component_clause,[],[f98])).
% 1.44/0.54  fof(f98,plain,(
% 1.44/0.54    spl4_6 <=> k1_xboole_0 = sK2),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.44/0.54  fof(f159,plain,(
% 1.44/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl4_3),
% 1.44/0.54    inference(resolution,[],[f79,f45])).
% 1.44/0.54  fof(f45,plain,(
% 1.44/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f30])).
% 1.44/0.54  fof(f30,plain,(
% 1.44/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.44/0.54    inference(nnf_transformation,[],[f5])).
% 1.44/0.54  fof(f5,axiom,(
% 1.44/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.44/0.54  fof(f79,plain,(
% 1.44/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_3),
% 1.44/0.54    inference(avatar_component_clause,[],[f78])).
% 1.44/0.54  fof(f78,plain,(
% 1.44/0.54    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.44/0.54  fof(f383,plain,(
% 1.44/0.54    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl4_2 | ~spl4_6)),
% 1.44/0.54    inference(forward_demodulation,[],[f76,f100])).
% 1.44/0.54  fof(f76,plain,(
% 1.44/0.54    ~v1_funct_2(sK3,sK0,sK2) | spl4_2),
% 1.44/0.54    inference(avatar_component_clause,[],[f74])).
% 1.44/0.54  fof(f74,plain,(
% 1.44/0.54    spl4_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.44/0.54  fof(f336,plain,(
% 1.44/0.54    spl4_2 | ~spl4_5 | ~spl4_7),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f335])).
% 1.44/0.54  fof(f335,plain,(
% 1.44/0.54    $false | (spl4_2 | ~spl4_5 | ~spl4_7)),
% 1.44/0.54    inference(subsumption_resolution,[],[f334,f332])).
% 1.44/0.54  fof(f332,plain,(
% 1.44/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (spl4_2 | ~spl4_5)),
% 1.44/0.54    inference(subsumption_resolution,[],[f278,f44])).
% 1.44/0.54  fof(f278,plain,(
% 1.44/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_5)),
% 1.44/0.54    inference(resolution,[],[f211,f67])).
% 1.44/0.54  fof(f67,plain,(
% 1.44/0.54    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.44/0.54    inference(equality_resolution,[],[f54])).
% 1.44/0.54  fof(f54,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f33])).
% 1.44/0.54  fof(f211,plain,(
% 1.44/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f173,f191])).
% 1.44/0.54  fof(f191,plain,(
% 1.44/0.54    k1_xboole_0 = sK3 | ~spl4_5),
% 1.44/0.54    inference(resolution,[],[f183,f43])).
% 1.44/0.54  fof(f183,plain,(
% 1.44/0.54    r1_tarski(sK3,k1_xboole_0) | ~spl4_5),
% 1.44/0.54    inference(forward_demodulation,[],[f178,f61])).
% 1.44/0.54  fof(f61,plain,(
% 1.44/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.44/0.54    inference(equality_resolution,[],[f41])).
% 1.44/0.54  fof(f41,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.44/0.54    inference(cnf_transformation,[],[f29])).
% 1.44/0.54  fof(f178,plain,(
% 1.44/0.54    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_5),
% 1.44/0.54    inference(backward_demodulation,[],[f111,f89])).
% 1.44/0.54  fof(f89,plain,(
% 1.44/0.54    k1_xboole_0 = sK0 | ~spl4_5),
% 1.44/0.54    inference(avatar_component_clause,[],[f87])).
% 1.44/0.54  fof(f111,plain,(
% 1.44/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.44/0.54    inference(resolution,[],[f36,f45])).
% 1.44/0.54  fof(f36,plain,(
% 1.44/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.54    inference(cnf_transformation,[],[f27])).
% 1.44/0.54  fof(f27,plain,(
% 1.44/0.54    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f26])).
% 1.44/0.54  fof(f26,plain,(
% 1.44/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f17,plain,(
% 1.44/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.44/0.54    inference(flattening,[],[f16])).
% 1.44/0.54  fof(f16,plain,(
% 1.44/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.44/0.54    inference(ennf_transformation,[],[f15])).
% 1.44/0.54  fof(f15,negated_conjecture,(
% 1.44/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.44/0.54    inference(negated_conjecture,[],[f14])).
% 1.44/0.54  fof(f14,conjecture,(
% 1.44/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.44/0.54  fof(f173,plain,(
% 1.44/0.54    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f76,f89])).
% 1.44/0.54  fof(f334,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl4_5 | ~spl4_7)),
% 1.44/0.54    inference(forward_demodulation,[],[f333,f89])).
% 1.44/0.54  fof(f333,plain,(
% 1.44/0.54    sK0 = k1_relset_1(sK0,sK2,k1_xboole_0) | (~spl4_5 | ~spl4_7)),
% 1.44/0.54    inference(forward_demodulation,[],[f103,f191])).
% 1.44/0.54  fof(f103,plain,(
% 1.44/0.54    sK0 = k1_relset_1(sK0,sK2,sK3) | ~spl4_7),
% 1.44/0.54    inference(avatar_component_clause,[],[f102])).
% 1.44/0.54  fof(f102,plain,(
% 1.44/0.54    spl4_7 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.44/0.54  fof(f320,plain,(
% 1.44/0.54    spl4_3 | ~spl4_4 | ~spl4_5),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f319])).
% 1.44/0.54  fof(f319,plain,(
% 1.44/0.54    $false | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(subsumption_resolution,[],[f318,f63])).
% 1.44/0.54  fof(f63,plain,(
% 1.44/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.54    inference(equality_resolution,[],[f47])).
% 1.44/0.54  fof(f47,plain,(
% 1.44/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  fof(f32,plain,(
% 1.44/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.54    inference(flattening,[],[f31])).
% 1.44/0.54  fof(f31,plain,(
% 1.44/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.54    inference(nnf_transformation,[],[f1])).
% 1.44/0.54  fof(f1,axiom,(
% 1.44/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.54  fof(f318,plain,(
% 1.44/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(forward_demodulation,[],[f317,f304])).
% 1.44/0.54  fof(f304,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f218,f303])).
% 1.44/0.54  fof(f303,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(subsumption_resolution,[],[f291,f44])).
% 1.44/0.54  fof(f291,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(resolution,[],[f219,f68])).
% 1.44/0.54  fof(f68,plain,(
% 1.44/0.54    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.44/0.54    inference(equality_resolution,[],[f52])).
% 1.44/0.54  fof(f52,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f33])).
% 1.44/0.54  fof(f219,plain,(
% 1.44/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f187,f191])).
% 1.44/0.54  fof(f187,plain,(
% 1.44/0.54    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f171,f84])).
% 1.44/0.54  fof(f84,plain,(
% 1.44/0.54    k1_xboole_0 = sK1 | ~spl4_4),
% 1.44/0.54    inference(avatar_component_clause,[],[f83])).
% 1.44/0.54  fof(f83,plain,(
% 1.44/0.54    spl4_4 <=> k1_xboole_0 = sK1),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.44/0.54  fof(f171,plain,(
% 1.44/0.54    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl4_5),
% 1.44/0.54    inference(backward_demodulation,[],[f35,f89])).
% 1.44/0.54  fof(f35,plain,(
% 1.44/0.54    v1_funct_2(sK3,sK0,sK1)),
% 1.44/0.54    inference(cnf_transformation,[],[f27])).
% 1.44/0.54  fof(f218,plain,(
% 1.44/0.54    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f186,f191])).
% 1.44/0.54  fof(f186,plain,(
% 1.44/0.54    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f176,f84])).
% 1.44/0.54  fof(f176,plain,(
% 1.44/0.54    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl4_5),
% 1.44/0.54    inference(backward_demodulation,[],[f107,f89])).
% 1.44/0.54  fof(f107,plain,(
% 1.44/0.54    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.44/0.54    inference(resolution,[],[f36,f58])).
% 1.44/0.54  fof(f58,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f24])).
% 1.44/0.54  fof(f24,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f10])).
% 1.44/0.54  fof(f10,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.44/0.54  fof(f317,plain,(
% 1.44/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl4_3 | ~spl4_5)),
% 1.44/0.54    inference(forward_demodulation,[],[f316,f191])).
% 1.44/0.54  fof(f316,plain,(
% 1.44/0.54    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | (spl4_3 | ~spl4_5)),
% 1.44/0.54    inference(forward_demodulation,[],[f136,f89])).
% 1.44/0.54  fof(f136,plain,(
% 1.44/0.54    ~r1_tarski(k1_relat_1(sK3),sK0) | spl4_3),
% 1.44/0.54    inference(subsumption_resolution,[],[f135,f106])).
% 1.44/0.54  fof(f106,plain,(
% 1.44/0.54    v1_relat_1(sK3)),
% 1.44/0.54    inference(resolution,[],[f36,f59])).
% 1.44/0.54  fof(f59,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f25,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f8])).
% 1.44/0.54  fof(f8,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.44/0.54  fof(f135,plain,(
% 1.44/0.54    ~r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl4_3),
% 1.44/0.54    inference(subsumption_resolution,[],[f133,f113])).
% 1.44/0.54  fof(f113,plain,(
% 1.44/0.54    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.44/0.54    inference(backward_demodulation,[],[f37,f110])).
% 1.44/0.54  fof(f110,plain,(
% 1.44/0.54    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.44/0.54    inference(resolution,[],[f36,f50])).
% 1.44/0.54  fof(f50,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f19])).
% 1.44/0.54  fof(f19,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f11])).
% 1.44/0.54  fof(f11,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.44/0.54  fof(f37,plain,(
% 1.44/0.54    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f27])).
% 1.44/0.54  fof(f133,plain,(
% 1.44/0.54    ~r1_tarski(k2_relat_1(sK3),sK2) | ~r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl4_3),
% 1.44/0.54    inference(resolution,[],[f80,f57])).
% 1.44/0.54  fof(f57,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f23])).
% 1.44/0.54  fof(f23,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.44/0.54    inference(flattening,[],[f22])).
% 1.44/0.54  fof(f22,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.44/0.54    inference(ennf_transformation,[],[f12])).
% 1.44/0.54  fof(f12,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.44/0.54  fof(f80,plain,(
% 1.44/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_3),
% 1.44/0.54    inference(avatar_component_clause,[],[f78])).
% 1.44/0.54  fof(f307,plain,(
% 1.44/0.54    ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f306])).
% 1.44/0.54  fof(f306,plain,(
% 1.44/0.54    $false | (~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7)),
% 1.44/0.54    inference(subsumption_resolution,[],[f305,f212])).
% 1.44/0.54  fof(f212,plain,(
% 1.44/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl4_5 | spl4_7)),
% 1.44/0.54    inference(backward_demodulation,[],[f175,f191])).
% 1.44/0.54  fof(f175,plain,(
% 1.44/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl4_5 | spl4_7)),
% 1.44/0.54    inference(backward_demodulation,[],[f104,f89])).
% 1.44/0.54  fof(f104,plain,(
% 1.44/0.54    sK0 != k1_relset_1(sK0,sK2,sK3) | spl4_7),
% 1.44/0.54    inference(avatar_component_clause,[],[f102])).
% 1.44/0.54  fof(f305,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f213,f304])).
% 1.44/0.54  fof(f213,plain,(
% 1.44/0.54    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl4_3 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f180,f191])).
% 1.44/0.54  fof(f180,plain,(
% 1.44/0.54    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl4_3 | ~spl4_5)),
% 1.44/0.54    inference(backward_demodulation,[],[f155,f89])).
% 1.44/0.54  fof(f155,plain,(
% 1.44/0.54    k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) | ~spl4_3),
% 1.44/0.54    inference(resolution,[],[f79,f58])).
% 1.44/0.54  fof(f162,plain,(
% 1.44/0.54    ~spl4_3 | spl4_4 | spl4_7),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f161])).
% 1.44/0.54  fof(f161,plain,(
% 1.44/0.54    $false | (~spl4_3 | spl4_4 | spl4_7)),
% 1.44/0.54    inference(subsumption_resolution,[],[f160,f104])).
% 1.44/0.54  fof(f160,plain,(
% 1.44/0.54    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl4_3 | spl4_4)),
% 1.44/0.54    inference(forward_demodulation,[],[f155,f112])).
% 1.44/0.54  fof(f112,plain,(
% 1.44/0.54    sK0 = k1_relat_1(sK3) | spl4_4),
% 1.44/0.54    inference(forward_demodulation,[],[f107,f95])).
% 1.44/0.54  fof(f95,plain,(
% 1.44/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 1.44/0.54    inference(subsumption_resolution,[],[f94,f36])).
% 1.44/0.54  fof(f94,plain,(
% 1.44/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_4),
% 1.44/0.54    inference(subsumption_resolution,[],[f93,f85])).
% 1.44/0.54  fof(f85,plain,(
% 1.44/0.54    k1_xboole_0 != sK1 | spl4_4),
% 1.44/0.54    inference(avatar_component_clause,[],[f83])).
% 1.44/0.54  fof(f93,plain,(
% 1.44/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.54    inference(resolution,[],[f35,f51])).
% 1.44/0.54  fof(f51,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f33])).
% 1.44/0.54  fof(f139,plain,(
% 1.44/0.54    spl4_3 | spl4_4),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f138])).
% 1.44/0.54  fof(f138,plain,(
% 1.44/0.54    $false | (spl4_3 | spl4_4)),
% 1.44/0.54    inference(subsumption_resolution,[],[f137,f63])).
% 1.44/0.54  fof(f137,plain,(
% 1.44/0.54    ~r1_tarski(sK0,sK0) | (spl4_3 | spl4_4)),
% 1.44/0.54    inference(forward_demodulation,[],[f136,f112])).
% 1.44/0.54  fof(f105,plain,(
% 1.44/0.54    ~spl4_3 | spl4_6 | ~spl4_7 | spl4_2),
% 1.44/0.54    inference(avatar_split_clause,[],[f96,f74,f102,f98,f78])).
% 1.44/0.54  fof(f96,plain,(
% 1.44/0.54    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_2),
% 1.44/0.54    inference(resolution,[],[f76,f53])).
% 1.44/0.54  fof(f53,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f33])).
% 1.44/0.54  fof(f92,plain,(
% 1.44/0.54    spl4_1),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f91])).
% 1.44/0.54  fof(f91,plain,(
% 1.44/0.54    $false | spl4_1),
% 1.44/0.54    inference(subsumption_resolution,[],[f72,f34])).
% 1.44/0.54  fof(f34,plain,(
% 1.44/0.54    v1_funct_1(sK3)),
% 1.44/0.54    inference(cnf_transformation,[],[f27])).
% 1.44/0.54  fof(f72,plain,(
% 1.44/0.54    ~v1_funct_1(sK3) | spl4_1),
% 1.44/0.54    inference(avatar_component_clause,[],[f70])).
% 1.44/0.54  fof(f70,plain,(
% 1.44/0.54    spl4_1 <=> v1_funct_1(sK3)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.44/0.54  fof(f90,plain,(
% 1.44/0.54    ~spl4_4 | spl4_5),
% 1.44/0.54    inference(avatar_split_clause,[],[f38,f87,f83])).
% 1.44/0.54  fof(f38,plain,(
% 1.44/0.54    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.44/0.54    inference(cnf_transformation,[],[f27])).
% 1.44/0.54  fof(f81,plain,(
% 1.44/0.54    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.44/0.54    inference(avatar_split_clause,[],[f39,f78,f74,f70])).
% 1.44/0.54  fof(f39,plain,(
% 1.44/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 1.44/0.54    inference(cnf_transformation,[],[f27])).
% 1.44/0.54  % SZS output end Proof for theBenchmark
% 1.44/0.54  % (18782)------------------------------
% 1.44/0.54  % (18782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (18782)Termination reason: Refutation
% 1.44/0.54  
% 1.44/0.54  % (18782)Memory used [KB]: 10746
% 1.44/0.54  % (18782)Time elapsed: 0.128 s
% 1.44/0.54  % (18782)------------------------------
% 1.44/0.54  % (18782)------------------------------
% 1.44/0.54  % (18770)Success in time 0.192 s
%------------------------------------------------------------------------------
