%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 369 expanded)
%              Number of leaves         :   46 ( 137 expanded)
%              Depth                    :   17
%              Number of atoms          :  612 (1649 expanded)
%              Number of equality atoms :   55 (  87 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f708,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f137,f140,f262,f266,f321,f324,f326,f328,f330,f392,f406,f410,f412,f487,f629,f659,f670,f685,f699,f707])).

fof(f707,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | spl6_27 ),
    inference(resolution,[],[f696,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f696,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_27 ),
    inference(resolution,[],[f515,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f515,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl6_27
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f699,plain,(
    spl6_37 ),
    inference(avatar_contradiction_clause,[],[f697])).

fof(f697,plain,
    ( $false
    | spl6_37 ),
    inference(resolution,[],[f686,f65])).

fof(f686,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl6_37 ),
    inference(resolution,[],[f684,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f684,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_37 ),
    inference(avatar_component_clause,[],[f682])).

fof(f682,plain,
    ( spl6_37
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f685,plain,
    ( ~ spl6_27
    | ~ spl6_37
    | spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f680,f241,f118,f682,f513])).

fof(f118,plain,
    ( spl6_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f241,plain,
    ( spl6_10
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f680,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(superposition,[],[f107,f243])).

fof(f243,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f241])).

fof(f107,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f670,plain,
    ( ~ spl6_19
    | spl6_10
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f668,f622,f241,f318])).

fof(f318,plain,
    ( spl6_19
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f622,plain,
    ( spl6_32
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f668,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_32 ),
    inference(superposition,[],[f92,f624])).

fof(f624,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f622])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f659,plain,
    ( ~ spl6_13
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f657])).

fof(f657,plain,
    ( $false
    | ~ spl6_13
    | spl6_33 ),
    inference(resolution,[],[f628,f333])).

fof(f333,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f66,f261])).

fof(f261,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl6_13
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f66,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f628,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl6_33 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl6_33
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f629,plain,
    ( ~ spl6_18
    | ~ spl6_22
    | ~ spl6_19
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_17
    | spl6_32
    | ~ spl6_33
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f620,f259,f626,f622,f310,f377,f306,f318,f381,f314])).

fof(f314,plain,
    ( spl6_18
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f381,plain,
    ( spl6_22
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f306,plain,
    ( spl6_16
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f377,plain,
    ( spl6_21
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f310,plain,
    ( spl6_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f620,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl6_13 ),
    inference(superposition,[],[f95,f261])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f487,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl6_1
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(resolution,[],[f455,f123])).

fof(f123,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f105,f103])).

fof(f103,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f71,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f68,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f105,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f71])).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f455,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl6_1
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f116,f452])).

fof(f452,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(resolution,[],[f443,f159])).

fof(f159,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl6_4 ),
    inference(resolution,[],[f86,f136])).

fof(f136,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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

fof(f443,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(resolution,[],[f440,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f440,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(resolution,[],[f428,f192])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f96,f142])).

fof(f142,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_4 ),
    inference(resolution,[],[f141,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f141,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_4 ),
    inference(resolution,[],[f136,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f428,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f414,f164])).

fof(f164,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl6_4 ),
    inference(resolution,[],[f159,f151])).

fof(f151,plain,
    ( ! [X2,X1] : r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2)
    | ~ spl6_4 ),
    inference(resolution,[],[f149,f88])).

fof(f149,plain,
    ( ! [X2,X3] : ~ r2_hidden(X2,k2_zfmisc_1(k1_xboole_0,X3))
    | ~ spl6_4 ),
    inference(resolution,[],[f146,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f146,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))
    | ~ spl6_4 ),
    inference(resolution,[],[f142,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f414,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f62,f387])).

fof(f387,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl6_23
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f116,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f412,plain,(
    spl6_22 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | spl6_22 ),
    inference(resolution,[],[f383,f64])).

fof(f64,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f383,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f381])).

fof(f410,plain,(
    spl6_21 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | spl6_21 ),
    inference(resolution,[],[f379,f61])).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f379,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f377])).

fof(f406,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | spl6_24 ),
    inference(resolution,[],[f391,f105])).

fof(f391,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl6_24
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f392,plain,
    ( ~ spl6_16
    | ~ spl6_21
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_19
    | spl6_1
    | spl6_23
    | ~ spl6_24
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f375,f259,f389,f385,f114,f318,f381,f314,f310,f377,f306])).

fof(f375,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_13 ),
    inference(superposition,[],[f97,f261])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f330,plain,(
    spl6_19 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl6_19 ),
    inference(resolution,[],[f320,f65])).

fof(f320,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f318])).

fof(f328,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl6_17 ),
    inference(resolution,[],[f312,f62])).

fof(f312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f310])).

fof(f326,plain,(
    spl6_18 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl6_18 ),
    inference(resolution,[],[f316,f63])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f316,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f314])).

fof(f324,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl6_16 ),
    inference(resolution,[],[f308,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f308,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f306])).

fof(f321,plain,
    ( ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | spl6_11 ),
    inference(avatar_split_clause,[],[f302,f251,f318,f314,f310,f306])).

fof(f251,plain,
    ( spl6_11
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f302,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_11 ),
    inference(resolution,[],[f102,f253])).

fof(f253,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f251])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f266,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl6_12 ),
    inference(resolution,[],[f257,f104])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f257,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl6_12
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f262,plain,
    ( ~ spl6_11
    | ~ spl6_12
    | spl6_13 ),
    inference(avatar_split_clause,[],[f247,f259,f255,f251])).

fof(f247,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f99,f66])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f140,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f133,f122])).

fof(f122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f106,f103])).

fof(f106,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f73,f71])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f133,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f137,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f129,f135,f131])).

fof(f129,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f128,f70])).

fof(f70,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f128,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f80,f78])).

fof(f78,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f121,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f67,f118,f114])).

fof(f67,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:56:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (11531)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (11529)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (11525)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (11553)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (11545)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (11528)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (11526)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (11524)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (11539)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (11543)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (11532)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (11552)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (11527)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (11554)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (11535)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (11546)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (11551)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (11536)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (11544)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (11538)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (11549)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (11533)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (11537)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (11534)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (11541)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (11550)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (11548)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (11542)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.57  % (11547)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (11536)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f708,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f121,f137,f140,f262,f266,f321,f324,f326,f328,f330,f392,f406,f410,f412,f487,f629,f659,f670,f685,f699,f707])).
% 0.20/0.57  fof(f707,plain,(
% 0.20/0.57    spl6_27),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f705])).
% 0.20/0.57  fof(f705,plain,(
% 0.20/0.57    $false | spl6_27),
% 0.20/0.57    inference(resolution,[],[f696,f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45,f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.20/0.57    inference(negated_conjecture,[],[f22])).
% 0.20/0.57  fof(f22,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.20/0.57  fof(f696,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_27),
% 0.20/0.57    inference(resolution,[],[f515,f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.57  fof(f515,plain,(
% 0.20/0.57    ~v1_relat_1(sK3) | spl6_27),
% 0.20/0.57    inference(avatar_component_clause,[],[f513])).
% 0.20/0.57  fof(f513,plain,(
% 0.20/0.57    spl6_27 <=> v1_relat_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.57  fof(f699,plain,(
% 0.20/0.57    spl6_37),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f697])).
% 0.20/0.57  fof(f697,plain,(
% 0.20/0.57    $false | spl6_37),
% 0.20/0.57    inference(resolution,[],[f686,f65])).
% 0.20/0.57  fof(f686,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl6_37),
% 0.20/0.57    inference(resolution,[],[f684,f94])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.57  fof(f684,plain,(
% 0.20/0.57    ~v5_relat_1(sK3,sK0) | spl6_37),
% 0.20/0.57    inference(avatar_component_clause,[],[f682])).
% 0.20/0.57  fof(f682,plain,(
% 0.20/0.57    spl6_37 <=> v5_relat_1(sK3,sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.20/0.57  fof(f685,plain,(
% 0.20/0.57    ~spl6_27 | ~spl6_37 | spl6_2 | ~spl6_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f680,f241,f118,f682,f513])).
% 0.20/0.57  fof(f118,plain,(
% 0.20/0.57    spl6_2 <=> v2_funct_2(sK3,sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.57  fof(f241,plain,(
% 0.20/0.57    spl6_10 <=> sK0 = k2_relat_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.57  fof(f680,plain,(
% 0.20/0.57    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl6_10),
% 0.20/0.57    inference(superposition,[],[f107,f243])).
% 0.20/0.57  fof(f243,plain,(
% 0.20/0.57    sK0 = k2_relat_1(sK3) | ~spl6_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f241])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(equality_resolution,[],[f83])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.57  fof(f670,plain,(
% 0.20/0.57    ~spl6_19 | spl6_10 | ~spl6_32),
% 0.20/0.57    inference(avatar_split_clause,[],[f668,f622,f241,f318])).
% 0.20/0.57  fof(f318,plain,(
% 0.20/0.57    spl6_19 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.57  fof(f622,plain,(
% 0.20/0.57    spl6_32 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.57  fof(f668,plain,(
% 0.20/0.57    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_32),
% 0.20/0.57    inference(superposition,[],[f92,f624])).
% 0.20/0.57  fof(f624,plain,(
% 0.20/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl6_32),
% 0.20/0.57    inference(avatar_component_clause,[],[f622])).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.57  fof(f659,plain,(
% 0.20/0.57    ~spl6_13 | spl6_33),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f657])).
% 0.20/0.57  fof(f657,plain,(
% 0.20/0.57    $false | (~spl6_13 | spl6_33)),
% 0.20/0.57    inference(resolution,[],[f628,f333])).
% 0.20/0.57  fof(f333,plain,(
% 0.20/0.57    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl6_13),
% 0.20/0.57    inference(backward_demodulation,[],[f66,f261])).
% 0.20/0.57  fof(f261,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl6_13),
% 0.20/0.57    inference(avatar_component_clause,[],[f259])).
% 0.20/0.57  fof(f259,plain,(
% 0.20/0.57    spl6_13 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f628,plain,(
% 0.20/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl6_33),
% 0.20/0.57    inference(avatar_component_clause,[],[f626])).
% 0.20/0.57  fof(f626,plain,(
% 0.20/0.57    spl6_33 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.57  fof(f629,plain,(
% 0.20/0.57    ~spl6_18 | ~spl6_22 | ~spl6_19 | ~spl6_16 | ~spl6_21 | ~spl6_17 | spl6_32 | ~spl6_33 | ~spl6_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f620,f259,f626,f622,f310,f377,f306,f318,f381,f314])).
% 0.20/0.57  fof(f314,plain,(
% 0.20/0.57    spl6_18 <=> v1_funct_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.57  fof(f381,plain,(
% 0.20/0.57    spl6_22 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.57  fof(f306,plain,(
% 0.20/0.57    spl6_16 <=> v1_funct_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.57  fof(f377,plain,(
% 0.20/0.57    spl6_21 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.57  fof(f310,plain,(
% 0.20/0.57    spl6_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.57  fof(f620,plain,(
% 0.20/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl6_13),
% 0.20/0.57    inference(superposition,[],[f95,f261])).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 0.20/0.57  fof(f487,plain,(
% 0.20/0.57    spl6_1 | ~spl6_4 | ~spl6_23),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f486])).
% 0.20/0.57  fof(f486,plain,(
% 0.20/0.57    $false | (spl6_1 | ~spl6_4 | ~spl6_23)),
% 0.20/0.57    inference(resolution,[],[f455,f123])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    v2_funct_1(k1_xboole_0)),
% 0.20/0.57    inference(superposition,[],[f105,f103])).
% 0.20/0.57  fof(f103,plain,(
% 0.20/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.20/0.57    inference(definition_unfolding,[],[f68,f71])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,axiom,(
% 0.20/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f74,f71])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.57  fof(f455,plain,(
% 0.20/0.57    ~v2_funct_1(k1_xboole_0) | (spl6_1 | ~spl6_4 | ~spl6_23)),
% 0.20/0.57    inference(backward_demodulation,[],[f116,f452])).
% 0.20/0.57  fof(f452,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | (~spl6_4 | ~spl6_23)),
% 0.20/0.57    inference(resolution,[],[f443,f159])).
% 0.20/0.57  fof(f159,plain,(
% 0.20/0.57    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl6_4),
% 0.20/0.57    inference(resolution,[],[f86,f136])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f135])).
% 0.20/0.57  fof(f135,plain,(
% 0.20/0.57    spl6_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(flattening,[],[f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f443,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(sK2,X0)) ) | (~spl6_4 | ~spl6_23)),
% 0.20/0.57    inference(resolution,[],[f440,f88])).
% 0.20/0.57  fof(f88,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.57  fof(f440,plain,(
% 0.20/0.57    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | (~spl6_4 | ~spl6_23)),
% 0.20/0.57    inference(resolution,[],[f428,f192])).
% 0.20/0.57  fof(f192,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl6_4),
% 0.20/0.57    inference(resolution,[],[f96,f142])).
% 0.20/0.57  fof(f142,plain,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0) | ~spl6_4),
% 0.20/0.57    inference(resolution,[],[f141,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.57    inference(rectify,[],[f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.57    inference(nnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.57  fof(f141,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_4),
% 0.20/0.57    inference(resolution,[],[f136,f90])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.57  fof(f96,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.57  fof(f428,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_4 | ~spl6_23)),
% 0.20/0.57    inference(forward_demodulation,[],[f414,f164])).
% 0.20/0.57  fof(f164,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | ~spl6_4),
% 0.20/0.57    inference(resolution,[],[f159,f151])).
% 0.20/0.57  fof(f151,plain,(
% 0.20/0.57    ( ! [X2,X1] : (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2)) ) | ~spl6_4),
% 0.20/0.57    inference(resolution,[],[f149,f88])).
% 0.20/0.57  fof(f149,plain,(
% 0.20/0.57    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(k1_xboole_0,X3))) ) | ~spl6_4),
% 0.20/0.57    inference(resolution,[],[f146,f75])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f50])).
% 0.20/0.57  fof(f146,plain,(
% 0.20/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) ) | ~spl6_4),
% 0.20/0.57    inference(resolution,[],[f142,f79])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.20/0.57  fof(f414,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl6_23),
% 0.20/0.57    inference(backward_demodulation,[],[f62,f387])).
% 0.20/0.57  fof(f387,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl6_23),
% 0.20/0.57    inference(avatar_component_clause,[],[f385])).
% 0.20/0.57  fof(f385,plain,(
% 0.20/0.57    spl6_23 <=> k1_xboole_0 = sK0),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    ~v2_funct_1(sK2) | spl6_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f114])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    spl6_1 <=> v2_funct_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.57  fof(f412,plain,(
% 0.20/0.57    spl6_22),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f411])).
% 0.20/0.57  fof(f411,plain,(
% 0.20/0.57    $false | spl6_22),
% 0.20/0.57    inference(resolution,[],[f383,f64])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f383,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,sK1,sK0) | spl6_22),
% 0.20/0.57    inference(avatar_component_clause,[],[f381])).
% 0.20/0.57  fof(f410,plain,(
% 0.20/0.57    spl6_21),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f409])).
% 0.20/0.57  fof(f409,plain,(
% 0.20/0.57    $false | spl6_21),
% 0.20/0.57    inference(resolution,[],[f379,f61])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f379,plain,(
% 0.20/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl6_21),
% 0.20/0.57    inference(avatar_component_clause,[],[f377])).
% 0.20/0.57  fof(f406,plain,(
% 0.20/0.57    spl6_24),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f405])).
% 0.20/0.57  fof(f405,plain,(
% 0.20/0.57    $false | spl6_24),
% 0.20/0.57    inference(resolution,[],[f391,f105])).
% 0.20/0.57  fof(f391,plain,(
% 0.20/0.57    ~v2_funct_1(k6_partfun1(sK0)) | spl6_24),
% 0.20/0.57    inference(avatar_component_clause,[],[f389])).
% 0.20/0.57  fof(f389,plain,(
% 0.20/0.57    spl6_24 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.57  fof(f392,plain,(
% 0.20/0.57    ~spl6_16 | ~spl6_21 | ~spl6_17 | ~spl6_18 | ~spl6_22 | ~spl6_19 | spl6_1 | spl6_23 | ~spl6_24 | ~spl6_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f375,f259,f389,f385,f114,f318,f381,f314,f310,f377,f306])).
% 0.20/0.57  fof(f375,plain,(
% 0.20/0.57    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl6_13),
% 0.20/0.57    inference(superposition,[],[f97,f261])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.57    inference(flattening,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.57    inference(ennf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 0.20/0.57  fof(f330,plain,(
% 0.20/0.57    spl6_19),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f329])).
% 0.20/0.57  fof(f329,plain,(
% 0.20/0.57    $false | spl6_19),
% 0.20/0.57    inference(resolution,[],[f320,f65])).
% 0.20/0.57  fof(f320,plain,(
% 0.20/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f318])).
% 0.20/0.57  fof(f328,plain,(
% 0.20/0.57    spl6_17),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f327])).
% 0.20/0.57  fof(f327,plain,(
% 0.20/0.57    $false | spl6_17),
% 0.20/0.57    inference(resolution,[],[f312,f62])).
% 0.20/0.57  fof(f312,plain,(
% 0.20/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_17),
% 0.20/0.57    inference(avatar_component_clause,[],[f310])).
% 0.20/0.57  fof(f326,plain,(
% 0.20/0.57    spl6_18),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f325])).
% 0.20/0.57  fof(f325,plain,(
% 0.20/0.57    $false | spl6_18),
% 0.20/0.57    inference(resolution,[],[f316,f63])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f316,plain,(
% 0.20/0.57    ~v1_funct_1(sK3) | spl6_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f314])).
% 0.20/0.57  fof(f324,plain,(
% 0.20/0.57    spl6_16),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f323])).
% 0.20/0.57  fof(f323,plain,(
% 0.20/0.57    $false | spl6_16),
% 0.20/0.57    inference(resolution,[],[f308,f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    v1_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f308,plain,(
% 0.20/0.57    ~v1_funct_1(sK2) | spl6_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f306])).
% 0.20/0.57  fof(f321,plain,(
% 0.20/0.57    ~spl6_16 | ~spl6_17 | ~spl6_18 | ~spl6_19 | spl6_11),
% 0.20/0.57    inference(avatar_split_clause,[],[f302,f251,f318,f314,f310,f306])).
% 0.20/0.57  fof(f251,plain,(
% 0.20/0.57    spl6_11 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.57  fof(f302,plain,(
% 0.20/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_11),
% 0.20/0.57    inference(resolution,[],[f102,f253])).
% 0.20/0.57  fof(f253,plain,(
% 0.20/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f251])).
% 0.20/0.57  fof(f102,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.57    inference(flattening,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.57  fof(f266,plain,(
% 0.20/0.57    spl6_12),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f265])).
% 0.20/0.57  fof(f265,plain,(
% 0.20/0.57    $false | spl6_12),
% 0.20/0.57    inference(resolution,[],[f257,f104])).
% 0.20/0.57  fof(f104,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f72,f71])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.20/0.57  fof(f257,plain,(
% 0.20/0.57    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_12),
% 0.20/0.57    inference(avatar_component_clause,[],[f255])).
% 0.20/0.57  fof(f255,plain,(
% 0.20/0.57    spl6_12 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.57  fof(f262,plain,(
% 0.20/0.57    ~spl6_11 | ~spl6_12 | spl6_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f247,f259,f255,f251])).
% 0.20/0.57  fof(f247,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(resolution,[],[f99,f66])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f59])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    spl6_3),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    $false | spl6_3),
% 0.20/0.57    inference(resolution,[],[f133,f122])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    v1_relat_1(k1_xboole_0)),
% 0.20/0.57    inference(superposition,[],[f106,f103])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f73,f71])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  fof(f133,plain,(
% 0.20/0.57    ~v1_relat_1(k1_xboole_0) | spl6_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f131])).
% 0.20/0.57  fof(f131,plain,(
% 0.20/0.57    spl6_3 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    ~spl6_3 | spl6_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f129,f135,f131])).
% 0.20/0.57  fof(f129,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f128,f70])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.57  fof(f128,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.57    inference(resolution,[],[f80,f78])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.58  fof(f121,plain,(
% 0.20/0.58    ~spl6_1 | ~spl6_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f67,f118,f114])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (11536)------------------------------
% 0.20/0.58  % (11536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (11536)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (11536)Memory used [KB]: 6524
% 0.20/0.58  % (11536)Time elapsed: 0.173 s
% 0.20/0.58  % (11536)------------------------------
% 0.20/0.58  % (11536)------------------------------
% 0.20/0.58  % (11523)Success in time 0.215 s
%------------------------------------------------------------------------------
