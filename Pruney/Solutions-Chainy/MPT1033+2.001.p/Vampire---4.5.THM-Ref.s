%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 224 expanded)
%              Number of leaves         :   15 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  328 (1659 expanded)
%              Number of equality atoms :   45 ( 323 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f72,f91,f100,f103,f159,f199,f204])).

fof(f204,plain,
    ( ~ spl4_2
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f202,f35])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f202,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_2
    | spl4_6 ),
    inference(forward_demodulation,[],[f201,f58])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f201,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f200,f188])).

fof(f188,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ spl4_2
    | spl4_6 ),
    inference(backward_demodulation,[],[f98,f58])).

fof(f98,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_6
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f200,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ v1_xboole_0(sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f61,f58])).

fof(f61,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f199,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f186,f35])).

fof(f186,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_2
    | spl4_3 ),
    inference(backward_demodulation,[],[f67,f58])).

fof(f67,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f159,plain,
    ( ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f151,f75])).

fof(f75,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f151,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f34,f146])).

fof(f146,plain,
    ( sK2 = sK3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f145,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f145,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f144,f32])).

fof(f32,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f144,plain,
    ( sK2 = sK3
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f142,f71])).

fof(f71,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_4
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f142,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f132,f28])).

fof(f132,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_partfun1(X1,sK0)
        | sK3 = X1
        | ~ r1_partfun1(X1,sK3)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f131,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | ~ v1_partfun1(X1,sK0)
        | sK3 = X1
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f126,f99])).

fof(f99,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f126,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK3)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X1,sK0)
      | sK3 = X1
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f34,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f103,plain,
    ( spl4_1
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f101,f54])).

fof(f54,plain,
    ( k1_xboole_0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(resolution,[],[f90,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f90,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f100,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f86,f97,f88])).

fof(f86,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f85,f29])).

fof(f85,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f80,f30])).

fof(f30,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f38,f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f91,plain,
    ( spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f84,f69,f88])).

fof(f84,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f83,f26])).

fof(f83,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f79,f27])).

fof(f27,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f38,f28])).

fof(f72,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f60,f69,f65])).

fof(f60,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f39,f28])).

fof(f59,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f33,f56,f52])).

fof(f33,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (24555)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.46  % (24547)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.47  % (24555)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f206,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f59,f72,f91,f100,f103,f159,f199,f204])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    ~spl4_2 | spl4_6),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    $false | (~spl4_2 | spl4_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f202,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0) | (~spl4_2 | spl4_6)),
% 0.20/0.48    inference(forward_demodulation,[],[f201,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl4_2 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    ~v1_xboole_0(sK0) | (~spl4_2 | spl4_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f200,f188])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    ~v1_partfun1(sK3,k1_xboole_0) | (~spl4_2 | spl4_6)),
% 0.20/0.48    inference(backward_demodulation,[],[f98,f58])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~v1_partfun1(sK3,sK0) | spl4_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl4_6 <=> v1_partfun1(sK3,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    v1_partfun1(sK3,k1_xboole_0) | ~v1_xboole_0(sK0) | ~spl4_2),
% 0.20/0.48    inference(forward_demodulation,[],[f61,f58])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    v1_partfun1(sK3,sK0) | ~v1_xboole_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f39,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    ~spl4_2 | spl4_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f198])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    $false | (~spl4_2 | spl4_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f186,f35])).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0) | (~spl4_2 | spl4_3)),
% 0.20/0.48    inference(backward_demodulation,[],[f67,f58])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ~v1_xboole_0(sK0) | spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl4_3 <=> v1_xboole_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    ~spl4_4 | ~spl4_6),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    $false | (~spl4_4 | ~spl4_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f151,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.48    inference(resolution,[],[f49,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(equality_resolution,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl4_4 | ~spl4_6)),
% 0.20/0.48    inference(backward_demodulation,[],[f34,f146])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    sK2 = sK3 | (~spl4_4 | ~spl4_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f145,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    sK2 = sK3 | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f144,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    r1_partfun1(sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    sK2 = sK3 | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f142,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    v1_partfun1(sK2,sK0) | ~spl4_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl4_4 <=> v1_partfun1(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,sK0) | sK2 = sK3 | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.20/0.48    inference(resolution,[],[f132,f28])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~r1_partfun1(X1,sK3) | ~v1_funct_1(X1)) ) | ~spl4_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f131,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1)) ) | ~spl4_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f126,f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    v1_partfun1(sK3,sK0) | ~spl4_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1)) )),
% 0.20/0.48    inference(resolution,[],[f43,f31])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl4_1 | ~spl4_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    $false | (spl4_1 | ~spl4_5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k1_xboole_0 != sK1 | spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl4_1 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~spl4_5),
% 0.20/0.48    inference(resolution,[],[f90,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | ~spl4_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl4_5 <=> v1_xboole_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl4_5 | spl4_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f86,f97,f88])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f85,f29])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ~v1_funct_1(sK3) | v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f38,f31])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    spl4_5 | spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f84,f69,f88])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f83,f26])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f79,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f38,f28])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ~spl4_3 | spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f60,f69,f65])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    v1_partfun1(sK2,sK0) | ~v1_xboole_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f39,f28])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ~spl4_1 | spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f56,f52])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (24555)------------------------------
% 0.20/0.48  % (24555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24555)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (24555)Memory used [KB]: 10746
% 0.20/0.48  % (24555)Time elapsed: 0.070 s
% 0.20/0.48  % (24555)------------------------------
% 0.20/0.48  % (24555)------------------------------
% 0.20/0.49  % (24529)Success in time 0.131 s
%------------------------------------------------------------------------------
