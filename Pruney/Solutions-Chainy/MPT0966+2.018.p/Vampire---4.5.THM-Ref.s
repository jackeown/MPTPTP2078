%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  183 (1338 expanded)
%              Number of leaves         :   24 ( 338 expanded)
%              Depth                    :   26
%              Number of atoms          :  619 (6440 expanded)
%              Number of equality atoms :  163 (2118 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f682,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f98,f100,f113,f140,f157,f170,f179,f434,f499,f536,f654,f675,f681])).

fof(f681,plain,
    ( ~ spl4_6
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | ~ spl4_6
    | spl4_11 ),
    inference(subsumption_resolution,[],[f679,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f679,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | ~ spl4_6
    | spl4_11 ),
    inference(forward_demodulation,[],[f151,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f151,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl4_11
  <=> r1_tarski(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f675,plain,
    ( ~ spl4_6
    | spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | ~ spl4_6
    | spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f139,f545])).

fof(f545,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f155,f108])).

fof(f155,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_12
  <=> sK2 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f139,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_10
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f654,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f652,f552])).

fof(f552,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f541,f134])).

fof(f134,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f541,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f540,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f540,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f87,f108])).

fof(f87,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f652,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_2
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f651,f68])).

fof(f651,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl4_2
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f640,f96])).

fof(f96,plain,
    ( k1_xboole_0 != sK0
    | spl4_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f640,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(resolution,[],[f584,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f584,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f583,f134])).

fof(f583,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f84,f108])).

fof(f84,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f536,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f535])).

fof(f535,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f534,f506])).

fof(f506,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f505,f274])).

fof(f274,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f230,f240])).

fof(f240,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f228,f54])).

fof(f228,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f199,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f199,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f195,f69])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f195,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f119,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f119,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f32])).

fof(f32,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f230,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(resolution,[],[f199,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f505,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f450,f69])).

fof(f450,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f335,f108])).

fof(f335,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f252,f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f252,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f190,f240])).

fof(f190,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f84,f97])).

fof(f534,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f533,f97])).

fof(f533,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f532,f108])).

fof(f532,plain,
    ( sK0 = k1_relset_1(sK0,sK2,k1_xboole_0)
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f177,f240])).

fof(f177,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_3
    | spl4_4 ),
    inference(forward_demodulation,[],[f171,f120])).

fof(f120,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(forward_demodulation,[],[f114,f103])).

fof(f103,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f102,f42])).

fof(f102,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f101,f93])).

fof(f93,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f101,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f41,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f114,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f42,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f171,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f87,f65])).

fof(f499,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f497,f54])).

fof(f497,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f496,f373])).

fof(f373,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f372,f274])).

fof(f372,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f363,f68])).

fof(f363,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f350,f258])).

fof(f258,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f201,f240])).

fof(f201,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f193,f92])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f193,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f114,f97])).

fof(f350,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f259,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f259,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f202,f240])).

fof(f202,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f188,f92])).

fof(f188,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f41,f97])).

fof(f496,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f495,f240])).

fof(f495,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f167,f97])).

fof(f167,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f166,f122])).

fof(f122,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f118,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f42,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f166,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f164,f121])).

fof(f121,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f43,f117])).

fof(f117,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f43,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f164,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(resolution,[],[f88,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f88,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f434,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f432,f274])).

fof(f432,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f431,f240])).

fof(f431,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f430,f69])).

fof(f430,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f429,f374])).

fof(f374,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f258,f373])).

fof(f429,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f428,f385])).

fof(f385,plain,
    ( k1_xboole_0 = sK2
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f384,f274])).

fof(f384,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f383,f69])).

fof(f383,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f336,f375])).

fof(f375,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f254,f373])).

fof(f254,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f196,f240])).

fof(f196,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f171,f97])).

fof(f336,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f252,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f428,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f206,f240])).

fof(f206,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f190,f75])).

fof(f179,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl4_3
    | spl4_4
    | spl4_7 ),
    inference(subsumption_resolution,[],[f177,f112])).

fof(f112,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_7
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f170,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f168,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f168,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_3
    | spl4_4 ),
    inference(forward_demodulation,[],[f167,f120])).

fof(f157,plain,
    ( ~ spl4_11
    | spl4_12 ),
    inference(avatar_split_clause,[],[f144,f153,f149])).

fof(f144,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(resolution,[],[f121,f53])).

fof(f140,plain,
    ( ~ spl4_10
    | spl4_9 ),
    inference(avatar_split_clause,[],[f125,f132,f137])).

fof(f125,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(resolution,[],[f122,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f113,plain,
    ( ~ spl4_3
    | spl4_6
    | ~ spl4_7
    | spl4_2 ),
    inference(avatar_split_clause,[],[f104,f82,f110,f106,f86])).

fof(f104,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_2 ),
    inference(resolution,[],[f84,f58])).

fof(f100,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f98,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f44,f95,f91])).

fof(f44,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f45,f86,f82,f78])).

fof(f45,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (27278)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (27284)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.48  % (27276)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (27269)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (27287)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (27290)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (27279)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (27265)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (27277)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (27275)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (27267)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (27271)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (27285)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (27271)Refutation not found, incomplete strategy% (27271)------------------------------
% 0.21/0.51  % (27271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27271)Memory used [KB]: 10618
% 0.21/0.51  % (27271)Time elapsed: 0.063 s
% 0.21/0.51  % (27271)------------------------------
% 0.21/0.51  % (27271)------------------------------
% 0.21/0.51  % (27276)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f682,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f89,f98,f100,f113,f140,f157,f170,f179,f434,f499,f536,f654,f675,f681])).
% 0.21/0.51  fof(f681,plain,(
% 0.21/0.51    ~spl4_6 | spl4_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f680])).
% 0.21/0.51  fof(f680,plain,(
% 0.21/0.51    $false | (~spl4_6 | spl4_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f679,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f679,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | (~spl4_6 | spl4_11)),
% 0.21/0.51    inference(forward_demodulation,[],[f151,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl4_6 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~r1_tarski(sK2,k2_relat_1(sK3)) | spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl4_11 <=> r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f675,plain,(
% 0.21/0.51    ~spl4_6 | spl4_10 | ~spl4_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f674])).
% 0.21/0.51  fof(f674,plain,(
% 0.21/0.51    $false | (~spl4_6 | spl4_10 | ~spl4_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f545])).
% 0.21/0.51  fof(f545,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK3) | (~spl4_6 | ~spl4_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f155,f108])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    sK2 = k2_relat_1(sK3) | ~spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl4_12 <=> sK2 = k2_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    k1_xboole_0 != k2_relat_1(sK3) | spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl4_10 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f654,plain,(
% 0.21/0.51    spl4_2 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f653])).
% 0.21/0.51  fof(f653,plain,(
% 0.21/0.51    $false | (spl4_2 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f652,f552])).
% 0.21/0.51  fof(f552,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_6 | ~spl4_9)),
% 0.21/0.51    inference(backward_demodulation,[],[f541,f134])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl4_9 <=> k1_xboole_0 = sK3),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f541,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f540,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f540,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl4_3 | ~spl4_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f87,f108])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f652,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl4_2 | spl4_5 | ~spl4_6 | ~spl4_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f651,f68])).
% 0.21/0.51  fof(f651,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl4_2 | spl4_5 | ~spl4_6 | ~spl4_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f640,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f640,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl4_2 | ~spl4_6 | ~spl4_9)),
% 0.21/0.51    inference(resolution,[],[f584,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f584,plain,(
% 0.21/0.51    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_2 | ~spl4_6 | ~spl4_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f583,f134])).
% 0.21/0.51  fof(f583,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl4_2 | ~spl4_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f84,f108])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK0,sK2) | spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl4_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f536,plain,(
% 0.21/0.51    spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f535])).
% 0.21/0.51  fof(f535,plain,(
% 0.21/0.51    $false | (spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f534,f506])).
% 0.21/0.51  fof(f506,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f505,f274])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 0.21/0.51    inference(forward_demodulation,[],[f230,f240])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | ~spl4_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f228,f54])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | ~spl4_5),
% 0.21/0.51    inference(resolution,[],[f199,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    r1_tarski(sK3,k1_xboole_0) | ~spl4_5),
% 0.21/0.51    inference(forward_demodulation,[],[f195,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_5),
% 0.21/0.51    inference(backward_demodulation,[],[f119,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f42,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f19])).
% 0.21/0.51  fof(f19,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 0.21/0.51    inference(resolution,[],[f199,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f505,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f450,f69])).
% 0.21/0.51  fof(f450,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f335,f108])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_5)),
% 0.21/0.51    inference(resolution,[],[f252,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f190,f240])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f84,f97])).
% 0.21/0.51  fof(f534,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f533,f97])).
% 0.21/0.51  fof(f533,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f532,f108])).
% 0.21/0.51  fof(f532,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK2,k1_xboole_0) | (~spl4_3 | spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f177,f240])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl4_3 | spl4_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f171,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | spl4_4),
% 0.21/0.51    inference(forward_demodulation,[],[f114,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f42])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(resolution,[],[f41,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f42,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) | ~spl4_3),
% 0.21/0.51    inference(resolution,[],[f87,f65])).
% 0.21/0.51  fof(f499,plain,(
% 0.21/0.51    spl4_3 | ~spl4_4 | ~spl4_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f498])).
% 0.21/0.51  fof(f498,plain,(
% 0.21/0.51    $false | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f497,f54])).
% 0.21/0.51  fof(f497,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f496,f373])).
% 0.21/0.51  fof(f373,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f372,f274])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f363,f68])).
% 0.21/0.51  fof(f363,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f350,f258])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f201,f240])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f193,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl4_5),
% 0.21/0.51    inference(backward_demodulation,[],[f114,f97])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(resolution,[],[f259,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f202,f240])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f188,f92])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl4_5),
% 0.21/0.51    inference(backward_demodulation,[],[f41,f97])).
% 0.21/0.51  fof(f496,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl4_3 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f495,f240])).
% 0.21/0.51  fof(f495,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | (spl4_3 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f167,f97])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK3),sK0) | spl4_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f166,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    v1_relat_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f42,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl4_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f164,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f43,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f42,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~r1_tarski(k2_relat_1(sK3),sK2) | ~r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl4_3),
% 0.21/0.51    inference(resolution,[],[f88,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f434,plain,(
% 0.21/0.51    spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f433])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    $false | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f432,f274])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f431,f240])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f430,f69])).
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f429,f374])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f258,f373])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f428,f385])).
% 0.21/0.51  fof(f385,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f384,f274])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f383,f69])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f336,f375])).
% 0.21/0.51  fof(f375,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f254,f373])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl4_3 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f196,f240])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl4_3 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f171,f97])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK2 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_5)),
% 0.21/0.51    inference(resolution,[],[f252,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f206,f240])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl4_2 | ~spl4_5)),
% 0.21/0.51    inference(resolution,[],[f190,f75])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ~spl4_3 | spl4_4 | spl4_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    $false | (~spl4_3 | spl4_4 | spl4_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f177,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    sK0 != k1_relset_1(sK0,sK2,sK3) | spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl4_7 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    spl4_3 | spl4_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    $false | (spl4_3 | spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f168,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~r1_tarski(sK0,sK0) | (spl4_3 | spl4_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f167,f120])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~spl4_11 | spl4_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f144,f153,f149])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    sK2 = k2_relat_1(sK3) | ~r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.51    inference(resolution,[],[f121,f53])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ~spl4_10 | spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f125,f132,f137])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 != k2_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f122,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~spl4_3 | spl4_6 | ~spl4_7 | spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f104,f82,f110,f106,f86])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_2),
% 0.21/0.51    inference(resolution,[],[f84,f58])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl4_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    $false | spl4_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f80,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ~v1_funct_1(sK3) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl4_1 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ~spl4_4 | spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f95,f91])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f86,f82,f78])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (27276)------------------------------
% 0.21/0.51  % (27276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27276)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (27276)Memory used [KB]: 10746
% 0.21/0.51  % (27276)Time elapsed: 0.096 s
% 0.21/0.51  % (27276)------------------------------
% 0.21/0.51  % (27276)------------------------------
% 0.21/0.51  % (27272)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (27264)Success in time 0.155 s
%------------------------------------------------------------------------------
