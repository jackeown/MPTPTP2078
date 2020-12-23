%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:10 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 655 expanded)
%              Number of leaves         :   28 ( 173 expanded)
%              Depth                    :   19
%              Number of atoms          :  548 (3611 expanded)
%              Number of equality atoms :  108 ( 869 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2821,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f109,f177,f1204,f1298,f1309,f1418,f1917,f1992,f2014,f2813])).

fof(f2813,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f2812])).

fof(f2812,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f2811,f399])).

fof(f399,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f144,f344])).

fof(f344,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(resolution,[],[f279,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f279,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f274,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f274,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f146,f103])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f146,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41])).

fof(f41,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f144,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2811,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f2810,f344])).

fof(f2810,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f2809,f405])).

fof(f405,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f306,f344])).

fof(f306,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f142,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f142,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f50,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2809,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f2808,f344])).

fof(f2808,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f2807,f310])).

fof(f310,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f303,f69])).

fof(f303,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f51,f108])).

fof(f51,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f2807,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f2806,f2559])).

fof(f2559,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f378,f344])).

fof(f378,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f268,f108])).

fof(f268,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f49,f103])).

fof(f49,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f2806,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f2805,f344])).

fof(f2805,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f2804,f310])).

fof(f2804,plain,
    ( ~ v1_funct_2(sK3,sK2,k1_xboole_0)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1313,f103])).

fof(f1313,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_2 ),
    inference(superposition,[],[f219,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f219,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f218,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f218,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f211,f50])).

fof(f211,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(superposition,[],[f95,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f95,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2014,plain,
    ( spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f2013,f121,f102])).

fof(f121,plain,
    ( spl4_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f2013,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f873,f50])).

fof(f873,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f1992,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f1991])).

fof(f1991,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_7
    | spl4_14 ),
    inference(subsumption_resolution,[],[f1990,f51])).

fof(f1990,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl4_3
    | ~ spl4_7
    | spl4_14 ),
    inference(forward_demodulation,[],[f1989,f618])).

fof(f618,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f614,f50])).

fof(f614,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(superposition,[],[f123,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f123,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1989,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_3
    | spl4_14 ),
    inference(subsumption_resolution,[],[f1988,f144])).

fof(f1988,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | spl4_14 ),
    inference(trivial_inequality_removal,[],[f1987])).

fof(f1987,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | spl4_14 ),
    inference(superposition,[],[f1985,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1985,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_3
    | spl4_14 ),
    inference(subsumption_resolution,[],[f1982,f1937])).

fof(f1937,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f98,f149])).

fof(f149,plain,(
    ! [X2] : k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,(
    ! [X2] :
      ( k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f50,f56])).

fof(f98,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1982,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_14 ),
    inference(superposition,[],[f1936,f63])).

fof(f1936,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_14 ),
    inference(forward_demodulation,[],[f216,f149])).

fof(f216,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl4_14
  <=> sK2 = k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1917,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f1913])).

fof(f1913,plain,
    ( $false
    | spl4_17 ),
    inference(resolution,[],[f1893,f1478])).

fof(f1478,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f1475,f1185])).

fof(f1185,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f1183,f167])).

fof(f167,plain,(
    ! [X7] : r1_tarski(k7_relat_1(sK3,X7),sK3) ),
    inference(resolution,[],[f144,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1183,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f168,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f168,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(sK3))
      | v1_relat_1(X8) ) ),
    inference(resolution,[],[f144,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1475,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_17 ),
    inference(resolution,[],[f1474,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1474,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f1473,f48])).

fof(f1473,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ v1_funct_1(sK3)
    | spl4_17 ),
    inference(subsumption_resolution,[],[f1471,f50])).

fof(f1471,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_17 ),
    inference(superposition,[],[f240,f56])).

fof(f240,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl4_17
  <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1893,plain,(
    ! [X10] : v5_relat_1(k7_relat_1(sK3,X10),sK1) ),
    inference(resolution,[],[f1866,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1866,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f148,f149])).

fof(f148,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f137,f48])).

fof(f137,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f50,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1418,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f1417])).

fof(f1417,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f1416,f48])).

fof(f1416,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f1415,f50])).

fof(f1415,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f1414,f166])).

fof(f166,plain,(
    ! [X6] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X6)),X6) ),
    inference(resolution,[],[f144,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f1414,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_16 ),
    inference(superposition,[],[f236,f56])).

fof(f236,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl4_16
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1309,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | ~ spl4_17
    | spl4_3 ),
    inference(avatar_split_clause,[],[f1306,f97,f238,f234,f230])).

fof(f230,plain,
    ( spl4_15
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1306,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_3 ),
    inference(resolution,[],[f99,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f99,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1298,plain,
    ( ~ spl4_3
    | ~ spl4_14
    | spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f1297,f102,f93,f214,f97])).

fof(f1297,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f1295,f104])).

fof(f104,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f1295,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2 ),
    inference(resolution,[],[f95,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1204,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f1193])).

fof(f1193,plain,
    ( $false
    | spl4_15 ),
    inference(resolution,[],[f1185,f1026])).

fof(f1026,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_15 ),
    inference(subsumption_resolution,[],[f1025,f48])).

fof(f1025,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | spl4_15 ),
    inference(subsumption_resolution,[],[f1024,f50])).

fof(f1024,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_15 ),
    inference(superposition,[],[f232,f56])).

fof(f232,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f230])).

fof(f177,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f175,f48])).

fof(f175,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f173,f50])).

fof(f173,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f109,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f52,f106,f102])).

fof(f52,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f97,f93,f89])).

fof(f53,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (628)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (631)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (638)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (635)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (634)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (621)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (630)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (642)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (644)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (626)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.23/0.54  % (624)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.54  % (625)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.23/0.54  % (623)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.23/0.54  % (639)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.23/0.54  % (637)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.51/0.55  % (629)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.51/0.55  % (622)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.56  % (622)Refutation not found, incomplete strategy% (622)------------------------------
% 1.51/0.56  % (622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (622)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (622)Memory used [KB]: 10618
% 1.51/0.56  % (622)Time elapsed: 0.129 s
% 1.51/0.56  % (622)------------------------------
% 1.51/0.56  % (622)------------------------------
% 1.51/0.56  % (645)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.51/0.57  % (636)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (640)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.51/0.58  % (641)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.51/0.58  % (645)Refutation not found, incomplete strategy% (645)------------------------------
% 1.51/0.58  % (645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (645)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (645)Memory used [KB]: 10618
% 1.51/0.58  % (645)Time elapsed: 0.138 s
% 1.51/0.58  % (645)------------------------------
% 1.51/0.58  % (645)------------------------------
% 1.51/0.64  % (644)Refutation found. Thanks to Tanya!
% 1.51/0.64  % SZS status Theorem for theBenchmark
% 1.51/0.64  % SZS output start Proof for theBenchmark
% 1.51/0.64  fof(f2821,plain,(
% 1.51/0.64    $false),
% 1.51/0.64    inference(avatar_sat_refutation,[],[f100,f109,f177,f1204,f1298,f1309,f1418,f1917,f1992,f2014,f2813])).
% 1.51/0.64  fof(f2813,plain,(
% 1.51/0.64    spl4_2 | ~spl4_4 | ~spl4_5),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f2812])).
% 1.51/0.64  fof(f2812,plain,(
% 1.51/0.64    $false | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(subsumption_resolution,[],[f2811,f399])).
% 1.51/0.64  fof(f399,plain,(
% 1.51/0.64    v1_relat_1(k1_xboole_0) | ~spl4_4),
% 1.51/0.64    inference(backward_demodulation,[],[f144,f344])).
% 1.51/0.64  fof(f344,plain,(
% 1.51/0.64    k1_xboole_0 = sK3 | ~spl4_4),
% 1.51/0.64    inference(resolution,[],[f279,f69])).
% 1.51/0.64  fof(f69,plain,(
% 1.51/0.64    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f32])).
% 1.51/0.64  fof(f32,plain,(
% 1.51/0.64    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.51/0.64    inference(ennf_transformation,[],[f1])).
% 1.51/0.64  fof(f1,axiom,(
% 1.51/0.64    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.51/0.64  fof(f279,plain,(
% 1.51/0.64    r1_tarski(sK3,k1_xboole_0) | ~spl4_4),
% 1.51/0.64    inference(forward_demodulation,[],[f274,f86])).
% 1.51/0.64  fof(f86,plain,(
% 1.51/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.51/0.64    inference(equality_resolution,[],[f66])).
% 1.51/0.64  fof(f66,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.51/0.64    inference(cnf_transformation,[],[f45])).
% 1.51/0.64  fof(f45,plain,(
% 1.51/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.51/0.64    inference(flattening,[],[f44])).
% 1.51/0.64  fof(f44,plain,(
% 1.51/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.51/0.64    inference(nnf_transformation,[],[f2])).
% 1.51/0.64  fof(f2,axiom,(
% 1.51/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.51/0.64  fof(f274,plain,(
% 1.51/0.64    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl4_4),
% 1.51/0.64    inference(backward_demodulation,[],[f146,f103])).
% 1.51/0.64  fof(f103,plain,(
% 1.51/0.64    k1_xboole_0 = sK1 | ~spl4_4),
% 1.51/0.64    inference(avatar_component_clause,[],[f102])).
% 1.51/0.64  fof(f102,plain,(
% 1.51/0.64    spl4_4 <=> k1_xboole_0 = sK1),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.51/0.64  fof(f146,plain,(
% 1.51/0.64    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.51/0.64    inference(resolution,[],[f50,f71])).
% 1.51/0.64  fof(f71,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f46])).
% 1.51/0.64  fof(f46,plain,(
% 1.51/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.51/0.64    inference(nnf_transformation,[],[f3])).
% 1.51/0.64  fof(f3,axiom,(
% 1.51/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.51/0.64  fof(f50,plain,(
% 1.51/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.51/0.64    inference(cnf_transformation,[],[f42])).
% 1.51/0.64  fof(f42,plain,(
% 1.51/0.64    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.51/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41])).
% 1.51/0.64  fof(f41,plain,(
% 1.51/0.64    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.51/0.64    introduced(choice_axiom,[])).
% 1.51/0.64  fof(f20,plain,(
% 1.51/0.64    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.51/0.64    inference(flattening,[],[f19])).
% 1.51/0.64  fof(f19,plain,(
% 1.51/0.64    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.51/0.64    inference(ennf_transformation,[],[f18])).
% 1.51/0.64  fof(f18,negated_conjecture,(
% 1.51/0.64    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.51/0.64    inference(negated_conjecture,[],[f17])).
% 1.51/0.64  fof(f17,conjecture,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.51/0.64  fof(f144,plain,(
% 1.51/0.64    v1_relat_1(sK3)),
% 1.51/0.64    inference(resolution,[],[f50,f79])).
% 1.51/0.64  fof(f79,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f39])).
% 1.51/0.64  fof(f39,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(ennf_transformation,[],[f10])).
% 1.51/0.64  fof(f10,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.51/0.64  fof(f2811,plain,(
% 1.51/0.64    ~v1_relat_1(k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(forward_demodulation,[],[f2810,f344])).
% 1.51/0.64  fof(f2810,plain,(
% 1.51/0.64    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(subsumption_resolution,[],[f2809,f405])).
% 1.51/0.64  fof(f405,plain,(
% 1.51/0.64    v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(backward_demodulation,[],[f306,f344])).
% 1.51/0.64  fof(f306,plain,(
% 1.51/0.64    v4_relat_1(sK3,k1_xboole_0) | ~spl4_5),
% 1.51/0.64    inference(backward_demodulation,[],[f142,f108])).
% 1.51/0.64  fof(f108,plain,(
% 1.51/0.64    k1_xboole_0 = sK0 | ~spl4_5),
% 1.51/0.64    inference(avatar_component_clause,[],[f106])).
% 1.51/0.64  fof(f106,plain,(
% 1.51/0.64    spl4_5 <=> k1_xboole_0 = sK0),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.51/0.64  fof(f142,plain,(
% 1.51/0.64    v4_relat_1(sK3,sK0)),
% 1.51/0.64    inference(resolution,[],[f50,f77])).
% 1.51/0.64  fof(f77,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f38])).
% 1.51/0.64  fof(f38,plain,(
% 1.51/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(ennf_transformation,[],[f11])).
% 1.51/0.64  fof(f11,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.51/0.64  fof(f2809,plain,(
% 1.51/0.64    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(forward_demodulation,[],[f2808,f344])).
% 1.51/0.64  fof(f2808,plain,(
% 1.51/0.64    ~v4_relat_1(sK3,k1_xboole_0) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(forward_demodulation,[],[f2807,f310])).
% 1.51/0.64  fof(f310,plain,(
% 1.51/0.64    k1_xboole_0 = sK2 | ~spl4_5),
% 1.51/0.64    inference(resolution,[],[f303,f69])).
% 1.51/0.64  fof(f303,plain,(
% 1.51/0.64    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.51/0.64    inference(backward_demodulation,[],[f51,f108])).
% 1.51/0.64  fof(f51,plain,(
% 1.51/0.64    r1_tarski(sK2,sK0)),
% 1.51/0.64    inference(cnf_transformation,[],[f42])).
% 1.51/0.64  fof(f2807,plain,(
% 1.51/0.64    ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(subsumption_resolution,[],[f2806,f2559])).
% 1.51/0.64  fof(f2559,plain,(
% 1.51/0.64    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(backward_demodulation,[],[f378,f344])).
% 1.51/0.64  fof(f378,plain,(
% 1.51/0.64    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(forward_demodulation,[],[f268,f108])).
% 1.51/0.64  fof(f268,plain,(
% 1.51/0.64    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 1.51/0.64    inference(backward_demodulation,[],[f49,f103])).
% 1.51/0.64  fof(f49,plain,(
% 1.51/0.64    v1_funct_2(sK3,sK0,sK1)),
% 1.51/0.64    inference(cnf_transformation,[],[f42])).
% 1.51/0.64  fof(f2806,plain,(
% 1.51/0.64    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(forward_demodulation,[],[f2805,f344])).
% 1.51/0.64  fof(f2805,plain,(
% 1.51/0.64    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.51/0.64    inference(forward_demodulation,[],[f2804,f310])).
% 1.51/0.64  fof(f2804,plain,(
% 1.51/0.64    ~v1_funct_2(sK3,sK2,k1_xboole_0) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_4)),
% 1.51/0.64    inference(forward_demodulation,[],[f1313,f103])).
% 1.51/0.64  fof(f1313,plain,(
% 1.51/0.64    ~v1_funct_2(sK3,sK2,sK1) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | spl4_2),
% 1.51/0.64    inference(superposition,[],[f219,f67])).
% 1.51/0.64  fof(f67,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f29])).
% 1.51/0.64  fof(f29,plain,(
% 1.51/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(flattening,[],[f28])).
% 1.51/0.64  fof(f28,plain,(
% 1.51/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.51/0.64    inference(ennf_transformation,[],[f6])).
% 1.51/0.64  fof(f6,axiom,(
% 1.51/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.51/0.64  fof(f219,plain,(
% 1.51/0.64    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.51/0.64    inference(subsumption_resolution,[],[f218,f48])).
% 1.51/0.64  fof(f48,plain,(
% 1.51/0.64    v1_funct_1(sK3)),
% 1.51/0.64    inference(cnf_transformation,[],[f42])).
% 1.51/0.64  fof(f218,plain,(
% 1.51/0.64    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(sK3) | spl4_2),
% 1.51/0.64    inference(subsumption_resolution,[],[f211,f50])).
% 1.51/0.64  fof(f211,plain,(
% 1.51/0.64    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_2),
% 1.51/0.64    inference(superposition,[],[f95,f56])).
% 1.51/0.64  fof(f56,plain,(
% 1.51/0.64    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f24])).
% 1.51/0.64  fof(f24,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.51/0.64    inference(flattening,[],[f23])).
% 1.51/0.64  fof(f23,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.51/0.64    inference(ennf_transformation,[],[f16])).
% 1.51/0.64  fof(f16,axiom,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.51/0.64  fof(f95,plain,(
% 1.51/0.64    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.51/0.64    inference(avatar_component_clause,[],[f93])).
% 1.51/0.64  fof(f93,plain,(
% 1.51/0.64    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.51/0.64  fof(f2014,plain,(
% 1.51/0.64    spl4_4 | spl4_7),
% 1.51/0.64    inference(avatar_split_clause,[],[f2013,f121,f102])).
% 1.51/0.64  fof(f121,plain,(
% 1.51/0.64    spl4_7 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.51/0.64  fof(f2013,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.51/0.64    inference(subsumption_resolution,[],[f873,f50])).
% 1.51/0.64  fof(f873,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.51/0.64    inference(resolution,[],[f49,f57])).
% 1.51/0.64  fof(f57,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f43])).
% 1.51/0.64  fof(f43,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(nnf_transformation,[],[f26])).
% 1.51/0.64  fof(f26,plain,(
% 1.51/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(flattening,[],[f25])).
% 1.51/0.64  fof(f25,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(ennf_transformation,[],[f14])).
% 1.51/0.64  fof(f14,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.51/0.64  fof(f1992,plain,(
% 1.51/0.64    ~spl4_3 | ~spl4_7 | spl4_14),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f1991])).
% 1.51/0.64  fof(f1991,plain,(
% 1.51/0.64    $false | (~spl4_3 | ~spl4_7 | spl4_14)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1990,f51])).
% 1.51/0.64  fof(f1990,plain,(
% 1.51/0.64    ~r1_tarski(sK2,sK0) | (~spl4_3 | ~spl4_7 | spl4_14)),
% 1.51/0.64    inference(forward_demodulation,[],[f1989,f618])).
% 1.51/0.64  fof(f618,plain,(
% 1.51/0.64    sK0 = k1_relat_1(sK3) | ~spl4_7),
% 1.51/0.64    inference(subsumption_resolution,[],[f614,f50])).
% 1.51/0.64  fof(f614,plain,(
% 1.51/0.64    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 1.51/0.64    inference(superposition,[],[f123,f63])).
% 1.51/0.64  fof(f63,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f27])).
% 1.51/0.64  fof(f27,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(ennf_transformation,[],[f12])).
% 1.51/0.64  fof(f12,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.51/0.64  fof(f123,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_7),
% 1.51/0.64    inference(avatar_component_clause,[],[f121])).
% 1.51/0.64  fof(f1989,plain,(
% 1.51/0.64    ~r1_tarski(sK2,k1_relat_1(sK3)) | (~spl4_3 | spl4_14)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1988,f144])).
% 1.51/0.64  fof(f1988,plain,(
% 1.51/0.64    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | spl4_14)),
% 1.51/0.64    inference(trivial_inequality_removal,[],[f1987])).
% 1.51/0.64  fof(f1987,plain,(
% 1.51/0.64    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | spl4_14)),
% 1.51/0.64    inference(superposition,[],[f1985,f68])).
% 1.51/0.64  fof(f68,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f31])).
% 1.51/0.64  fof(f31,plain,(
% 1.51/0.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(flattening,[],[f30])).
% 1.51/0.64  fof(f30,plain,(
% 1.51/0.64    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(ennf_transformation,[],[f9])).
% 1.51/0.64  fof(f9,axiom,(
% 1.51/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.51/0.64  fof(f1985,plain,(
% 1.51/0.64    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_3 | spl4_14)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1982,f1937])).
% 1.51/0.64  fof(f1937,plain,(
% 1.51/0.64    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.51/0.64    inference(forward_demodulation,[],[f98,f149])).
% 1.51/0.64  fof(f149,plain,(
% 1.51/0.64    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)) )),
% 1.51/0.64    inference(subsumption_resolution,[],[f138,f48])).
% 1.51/0.64  fof(f138,plain,(
% 1.51/0.64    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) | ~v1_funct_1(sK3)) )),
% 1.51/0.64    inference(resolution,[],[f50,f56])).
% 1.51/0.64  fof(f98,plain,(
% 1.51/0.64    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.51/0.64    inference(avatar_component_clause,[],[f97])).
% 1.51/0.64  fof(f97,plain,(
% 1.51/0.64    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.51/0.64  fof(f1982,plain,(
% 1.51/0.64    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_14),
% 1.51/0.64    inference(superposition,[],[f1936,f63])).
% 1.51/0.64  fof(f1936,plain,(
% 1.51/0.64    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_14),
% 1.51/0.64    inference(forward_demodulation,[],[f216,f149])).
% 1.51/0.64  fof(f216,plain,(
% 1.51/0.64    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_14),
% 1.51/0.64    inference(avatar_component_clause,[],[f214])).
% 1.51/0.64  fof(f214,plain,(
% 1.51/0.64    spl4_14 <=> sK2 = k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.51/0.64  fof(f1917,plain,(
% 1.51/0.64    spl4_17),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f1913])).
% 1.51/0.64  fof(f1913,plain,(
% 1.51/0.64    $false | spl4_17),
% 1.51/0.64    inference(resolution,[],[f1893,f1478])).
% 1.51/0.64  fof(f1478,plain,(
% 1.51/0.64    ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl4_17),
% 1.51/0.64    inference(subsumption_resolution,[],[f1475,f1185])).
% 1.51/0.64  fof(f1185,plain,(
% 1.51/0.64    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.51/0.64    inference(resolution,[],[f1183,f167])).
% 1.51/0.64  fof(f167,plain,(
% 1.51/0.64    ( ! [X7] : (r1_tarski(k7_relat_1(sK3,X7),sK3)) )),
% 1.51/0.64    inference(resolution,[],[f144,f76])).
% 1.51/0.64  fof(f76,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f37])).
% 1.51/0.64  fof(f37,plain,(
% 1.51/0.64    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(ennf_transformation,[],[f8])).
% 1.51/0.64  fof(f8,axiom,(
% 1.51/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.51/0.64  fof(f1183,plain,(
% 1.51/0.64    ( ! [X0] : (~r1_tarski(X0,sK3) | v1_relat_1(X0)) )),
% 1.51/0.64    inference(resolution,[],[f168,f72])).
% 1.51/0.64  fof(f72,plain,(
% 1.51/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f46])).
% 1.51/0.64  fof(f168,plain,(
% 1.51/0.64    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(sK3)) | v1_relat_1(X8)) )),
% 1.51/0.64    inference(resolution,[],[f144,f80])).
% 1.51/0.64  fof(f80,plain,(
% 1.51/0.64    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f40])).
% 1.51/0.64  fof(f40,plain,(
% 1.51/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.51/0.64    inference(ennf_transformation,[],[f4])).
% 1.51/0.64  fof(f4,axiom,(
% 1.51/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.51/0.64  fof(f1475,plain,(
% 1.51/0.64    ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_17),
% 1.51/0.64    inference(resolution,[],[f1474,f73])).
% 1.51/0.64  fof(f73,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f47])).
% 1.51/0.64  fof(f47,plain,(
% 1.51/0.64    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(nnf_transformation,[],[f35])).
% 1.51/0.64  fof(f35,plain,(
% 1.51/0.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(ennf_transformation,[],[f5])).
% 1.51/0.64  fof(f5,axiom,(
% 1.51/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.51/0.64  fof(f1474,plain,(
% 1.51/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | spl4_17),
% 1.51/0.64    inference(subsumption_resolution,[],[f1473,f48])).
% 1.51/0.64  fof(f1473,plain,(
% 1.51/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~v1_funct_1(sK3) | spl4_17),
% 1.51/0.64    inference(subsumption_resolution,[],[f1471,f50])).
% 1.51/0.64  fof(f1471,plain,(
% 1.51/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_17),
% 1.51/0.64    inference(superposition,[],[f240,f56])).
% 1.51/0.64  fof(f240,plain,(
% 1.51/0.64    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | spl4_17),
% 1.51/0.64    inference(avatar_component_clause,[],[f238])).
% 1.51/0.64  fof(f238,plain,(
% 1.51/0.64    spl4_17 <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.51/0.64  fof(f1893,plain,(
% 1.51/0.64    ( ! [X10] : (v5_relat_1(k7_relat_1(sK3,X10),sK1)) )),
% 1.51/0.64    inference(resolution,[],[f1866,f78])).
% 1.51/0.64  fof(f78,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f38])).
% 1.51/0.64  fof(f1866,plain,(
% 1.51/0.64    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.51/0.64    inference(forward_demodulation,[],[f148,f149])).
% 1.51/0.64  fof(f148,plain,(
% 1.51/0.64    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.51/0.64    inference(subsumption_resolution,[],[f137,f48])).
% 1.51/0.64  fof(f137,plain,(
% 1.51/0.64    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.51/0.64    inference(resolution,[],[f50,f55])).
% 1.51/0.64  fof(f55,plain,(
% 1.51/0.64    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f22])).
% 1.51/0.64  fof(f22,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.51/0.64    inference(flattening,[],[f21])).
% 1.51/0.64  fof(f21,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.51/0.64    inference(ennf_transformation,[],[f15])).
% 1.51/0.64  fof(f15,axiom,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.51/0.64  fof(f1418,plain,(
% 1.51/0.64    spl4_16),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f1417])).
% 1.51/0.64  fof(f1417,plain,(
% 1.51/0.64    $false | spl4_16),
% 1.51/0.64    inference(subsumption_resolution,[],[f1416,f48])).
% 1.51/0.64  fof(f1416,plain,(
% 1.51/0.64    ~v1_funct_1(sK3) | spl4_16),
% 1.51/0.64    inference(subsumption_resolution,[],[f1415,f50])).
% 1.51/0.64  fof(f1415,plain,(
% 1.51/0.64    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_16),
% 1.51/0.64    inference(subsumption_resolution,[],[f1414,f166])).
% 1.51/0.64  fof(f166,plain,(
% 1.51/0.64    ( ! [X6] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X6)),X6)) )),
% 1.51/0.64    inference(resolution,[],[f144,f75])).
% 1.51/0.64  fof(f75,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f36])).
% 1.51/0.64  fof(f36,plain,(
% 1.51/0.64    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(ennf_transformation,[],[f7])).
% 1.51/0.64  fof(f7,axiom,(
% 1.51/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.51/0.64  fof(f1414,plain,(
% 1.51/0.64    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_16),
% 1.51/0.64    inference(superposition,[],[f236,f56])).
% 1.51/0.64  fof(f236,plain,(
% 1.51/0.64    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_16),
% 1.51/0.64    inference(avatar_component_clause,[],[f234])).
% 1.51/0.64  fof(f234,plain,(
% 1.51/0.64    spl4_16 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.51/0.64  fof(f1309,plain,(
% 1.51/0.64    ~spl4_15 | ~spl4_16 | ~spl4_17 | spl4_3),
% 1.51/0.64    inference(avatar_split_clause,[],[f1306,f97,f238,f234,f230])).
% 1.51/0.64  fof(f230,plain,(
% 1.51/0.64    spl4_15 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.51/0.64  fof(f1306,plain,(
% 1.51/0.64    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_3),
% 1.51/0.64    inference(resolution,[],[f99,f70])).
% 1.51/0.64  fof(f70,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f34])).
% 2.25/0.64  fof(f34,plain,(
% 2.25/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.25/0.64    inference(flattening,[],[f33])).
% 2.25/0.64  fof(f33,plain,(
% 2.25/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.25/0.64    inference(ennf_transformation,[],[f13])).
% 2.25/0.64  fof(f13,axiom,(
% 2.25/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.25/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 2.25/0.64  fof(f99,plain,(
% 2.25/0.64    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 2.25/0.64    inference(avatar_component_clause,[],[f97])).
% 2.25/0.64  fof(f1298,plain,(
% 2.25/0.64    ~spl4_3 | ~spl4_14 | spl4_2 | spl4_4),
% 2.25/0.64    inference(avatar_split_clause,[],[f1297,f102,f93,f214,f97])).
% 2.25/0.64  fof(f1297,plain,(
% 2.25/0.64    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | spl4_4)),
% 2.25/0.64    inference(subsumption_resolution,[],[f1295,f104])).
% 2.25/0.64  fof(f104,plain,(
% 2.25/0.64    k1_xboole_0 != sK1 | spl4_4),
% 2.25/0.64    inference(avatar_component_clause,[],[f102])).
% 2.25/0.64  fof(f1295,plain,(
% 2.25/0.64    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_2),
% 2.25/0.64    inference(resolution,[],[f95,f59])).
% 2.25/0.64  fof(f59,plain,(
% 2.25/0.64    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.64    inference(cnf_transformation,[],[f43])).
% 2.25/0.64  fof(f1204,plain,(
% 2.25/0.64    spl4_15),
% 2.25/0.64    inference(avatar_contradiction_clause,[],[f1193])).
% 2.25/0.64  fof(f1193,plain,(
% 2.25/0.64    $false | spl4_15),
% 2.25/0.64    inference(resolution,[],[f1185,f1026])).
% 2.25/0.64  fof(f1026,plain,(
% 2.25/0.64    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_15),
% 2.25/0.64    inference(subsumption_resolution,[],[f1025,f48])).
% 2.25/0.64  fof(f1025,plain,(
% 2.25/0.64    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | spl4_15),
% 2.25/0.64    inference(subsumption_resolution,[],[f1024,f50])).
% 2.25/0.64  fof(f1024,plain,(
% 2.25/0.64    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_15),
% 2.25/0.64    inference(superposition,[],[f232,f56])).
% 2.25/0.64  fof(f232,plain,(
% 2.25/0.64    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_15),
% 2.25/0.64    inference(avatar_component_clause,[],[f230])).
% 2.25/0.64  fof(f177,plain,(
% 2.25/0.64    spl4_1),
% 2.25/0.64    inference(avatar_contradiction_clause,[],[f176])).
% 2.25/0.64  fof(f176,plain,(
% 2.25/0.64    $false | spl4_1),
% 2.25/0.64    inference(subsumption_resolution,[],[f175,f48])).
% 2.25/0.64  fof(f175,plain,(
% 2.25/0.64    ~v1_funct_1(sK3) | spl4_1),
% 2.25/0.64    inference(subsumption_resolution,[],[f173,f50])).
% 2.25/0.64  fof(f173,plain,(
% 2.25/0.64    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_1),
% 2.25/0.64    inference(resolution,[],[f91,f54])).
% 2.25/0.64  fof(f54,plain,(
% 2.25/0.64    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.25/0.64    inference(cnf_transformation,[],[f22])).
% 2.25/0.64  fof(f91,plain,(
% 2.25/0.64    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 2.25/0.64    inference(avatar_component_clause,[],[f89])).
% 2.25/0.64  fof(f89,plain,(
% 2.25/0.64    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.25/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.25/0.64  fof(f109,plain,(
% 2.25/0.64    ~spl4_4 | spl4_5),
% 2.25/0.64    inference(avatar_split_clause,[],[f52,f106,f102])).
% 2.25/0.64  fof(f52,plain,(
% 2.25/0.64    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.25/0.64    inference(cnf_transformation,[],[f42])).
% 2.25/0.64  fof(f100,plain,(
% 2.25/0.64    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 2.25/0.64    inference(avatar_split_clause,[],[f53,f97,f93,f89])).
% 2.25/0.64  fof(f53,plain,(
% 2.25/0.64    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.25/0.64    inference(cnf_transformation,[],[f42])).
% 2.25/0.64  % SZS output end Proof for theBenchmark
% 2.25/0.64  % (644)------------------------------
% 2.25/0.64  % (644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.64  % (644)Termination reason: Refutation
% 2.25/0.64  
% 2.25/0.64  % (644)Memory used [KB]: 6908
% 2.25/0.64  % (644)Time elapsed: 0.212 s
% 2.25/0.64  % (644)------------------------------
% 2.25/0.64  % (644)------------------------------
% 2.25/0.65  % (620)Success in time 0.287 s
%------------------------------------------------------------------------------
