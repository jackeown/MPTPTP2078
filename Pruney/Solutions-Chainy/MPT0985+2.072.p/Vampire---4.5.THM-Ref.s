%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 494 expanded)
%              Number of leaves         :   30 ( 157 expanded)
%              Depth                    :   14
%              Number of atoms          :  571 (1904 expanded)
%              Number of equality atoms :  115 ( 474 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f563,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f152,f154,f162,f200,f212,f217,f229,f235,f255,f257,f381,f433,f456,f542,f562])).

fof(f562,plain,
    ( spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(resolution,[],[f555,f184])).

fof(f184,plain,(
    ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(superposition,[],[f92,f169])).

fof(f169,plain,(
    ! [X1] : k1_xboole_0 = sK5(k1_xboole_0,X1) ),
    inference(resolution,[],[f164,f157])).

fof(f157,plain,(
    ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f87,f108])).

fof(f108,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f87,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK5(X0,X1),X0,X1)
      & v1_funct_1(sK5(X0,X1))
      & v5_relat_1(sK5(X0,X1),X1)
      & v4_relat_1(sK5(X0,X1),X0)
      & v1_relat_1(sK5(X0,X1))
      & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK5(X0,X1),X0,X1)
        & v1_funct_1(sK5(X0,X1))
        & v5_relat_1(sK5(X0,X1),X1)
        & v4_relat_1(sK5(X0,X1),X0)
        & v1_relat_1(sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f155,f64])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f72,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f92,plain,(
    ! [X0,X1] : v1_funct_2(sK5(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f54])).

fof(f555,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f546,f541])).

fof(f541,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(resolution,[],[f507,f164])).

fof(f507,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f470,f485])).

fof(f485,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(resolution,[],[f468,f164])).

fof(f468,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f459,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f459,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f60,f457])).

fof(f457,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f260,f390])).

fof(f390,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f260,f360])).

fof(f360,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl6_24
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f260,plain,
    ( sK2 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f199,f253])).

fof(f253,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl6_16
  <=> sK2 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f199,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_8
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f470,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f465,f108])).

fof(f465,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3))))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f259,f457])).

fof(f259,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f236,f253])).

fof(f236,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f211,f234])).

fof(f234,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl6_14
  <=> k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f211,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl6_10
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f546,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f385,f485])).

fof(f385,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f121,f360])).

fof(f121,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_2
  <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f542,plain,
    ( spl6_3
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | spl6_3
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(resolution,[],[f507,f506])).

fof(f506,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f469,f485])).

fof(f469,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f462,f108])).

fof(f462,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl6_3
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f125,f457])).

fof(f125,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_3
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f456,plain,
    ( ~ spl6_15
    | spl6_23
    | spl6_24 ),
    inference(avatar_split_clause,[],[f405,f358,f354,f247])).

fof(f247,plain,
    ( spl6_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f354,plain,
    ( spl6_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f405,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f59,f342])).

fof(f342,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | k1_relat_1(X5) = X3
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | k1_xboole_0 = X4
      | ~ v1_funct_2(X5,X3,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f288,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X2,X0) = X1
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f96,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f38,f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f59,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f433,plain,
    ( spl6_3
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | spl6_3
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(resolution,[],[f402,f125])).

fof(f402,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f259,f400])).

fof(f400,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_14
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f234,f366])).

fof(f366,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ spl6_14
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f234,f356])).

fof(f356,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f354])).

fof(f381,plain,
    ( spl6_2
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl6_2
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(resolution,[],[f365,f121])).

fof(f365,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f258,f356])).

fof(f258,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f237,f253])).

fof(f237,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ spl6_11
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f216,f234])).

fof(f216,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl6_11
  <=> v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f257,plain,(
    spl6_15 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl6_15 ),
    inference(resolution,[],[f249,f60])).

fof(f249,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f247])).

fof(f255,plain,
    ( ~ spl6_15
    | spl6_16 ),
    inference(avatar_split_clause,[],[f245,f251,f247])).

fof(f245,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(superposition,[],[f62,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f235,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_14 ),
    inference(avatar_split_clause,[],[f230,f232,f149,f145])).

fof(f145,plain,
    ( spl6_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f149,plain,
    ( spl6_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f230,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f229,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_9 ),
    inference(avatar_split_clause,[],[f227,f205,f149,f145])).

fof(f205,plain,
    ( spl6_9
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f227,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_9 ),
    inference(resolution,[],[f207,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f207,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f217,plain,
    ( ~ spl6_9
    | ~ spl6_1
    | spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f202,f197,f214,f115,f205])).

fof(f115,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f202,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_8 ),
    inference(superposition,[],[f76,f199])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f212,plain,
    ( ~ spl6_9
    | ~ spl6_1
    | spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f201,f197,f209,f115,f205])).

fof(f201,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_8 ),
    inference(superposition,[],[f77,f199])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f200,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f195,f197,f149,f145])).

fof(f195,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f80,f61])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f162,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f158,f60])).

fof(f158,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_6 ),
    inference(resolution,[],[f93,f147])).

fof(f147,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f154,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f151,f58])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f151,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f152,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f143,f115,f149,f145])).

fof(f143,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_1 ),
    inference(resolution,[],[f79,f117])).

fof(f117,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f126,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f63,f123,f119,f115])).

fof(f63,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (32137)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (32153)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (32145)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (32142)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (32157)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (32143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (32132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (32141)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (32134)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (32131)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (32152)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (32135)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (32140)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (32130)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (32140)Refutation not found, incomplete strategy% (32140)------------------------------
% 0.20/0.53  % (32140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32140)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32140)Memory used [KB]: 10618
% 0.20/0.53  % (32140)Time elapsed: 0.123 s
% 0.20/0.53  % (32140)------------------------------
% 0.20/0.53  % (32140)------------------------------
% 0.20/0.53  % (32151)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (32133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (32144)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (32159)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (32154)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (32142)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f563,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f126,f152,f154,f162,f200,f212,f217,f229,f235,f255,f257,f381,f433,f456,f542,f562])).
% 0.20/0.54  fof(f562,plain,(
% 0.20/0.54    spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f560])).
% 0.20/0.54  fof(f560,plain,(
% 0.20/0.54    $false | (spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(resolution,[],[f555,f184])).
% 0.20/0.54  fof(f184,plain,(
% 0.20/0.54    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) )),
% 0.20/0.54    inference(superposition,[],[f92,f169])).
% 0.20/0.54  fof(f169,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 = sK5(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f164,f157])).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    ( ! [X1] : (m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.54    inference(superposition,[],[f87,f108])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f85])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(flattening,[],[f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1) & v1_funct_1(sK5(X0,X1)) & v5_relat_1(sK5(X0,X1),X1) & v4_relat_1(sK5(X0,X1),X0) & v1_relat_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK5(X0,X1),X0,X1) & v1_funct_1(sK5(X0,X1)) & v5_relat_1(sK5(X0,X1),X1) & v4_relat_1(sK5(X0,X1),X0) & v1_relat_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 0.20/0.54  fof(f164,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f155,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f72,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f54])).
% 0.20/0.54  fof(f555,plain,(
% 0.20/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f546,f541])).
% 0.20/0.54  fof(f541,plain,(
% 0.20/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(resolution,[],[f507,f164])).
% 0.20/0.54  fof(f507,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f470,f485])).
% 0.20/0.54  fof(f485,plain,(
% 0.20/0.54    k1_xboole_0 = sK3 | (~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(resolution,[],[f468,f164])).
% 0.20/0.54  fof(f468,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(forward_demodulation,[],[f459,f107])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f459,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f60,f457])).
% 0.20/0.54  fof(f457,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | (~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f260,f390])).
% 0.20/0.54  fof(f390,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(k2_funct_1(sK3)) | (~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f260,f360])).
% 0.20/0.54  fof(f360,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~spl6_24),
% 0.20/0.54    inference(avatar_component_clause,[],[f358])).
% 0.20/0.54  fof(f358,plain,(
% 0.20/0.54    spl6_24 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.54  fof(f260,plain,(
% 0.20/0.54    sK2 = k1_relat_1(k2_funct_1(sK3)) | (~spl6_8 | ~spl6_16)),
% 0.20/0.54    inference(backward_demodulation,[],[f199,f253])).
% 0.20/0.54  fof(f253,plain,(
% 0.20/0.54    sK2 = k2_relat_1(sK3) | ~spl6_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f251])).
% 0.20/0.54  fof(f251,plain,(
% 0.20/0.54    spl6_16 <=> sK2 = k2_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.54  fof(f199,plain,(
% 0.20/0.54    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~spl6_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f197])).
% 0.20/0.54  fof(f197,plain,(
% 0.20/0.54    spl6_8 <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f21])).
% 0.20/0.54  fof(f21,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.54  fof(f470,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | (~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(forward_demodulation,[],[f465,f108])).
% 0.20/0.54  fof(f465,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) | (~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f259,f457])).
% 0.20/0.54  fof(f259,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | (~spl6_10 | ~spl6_14 | ~spl6_16)),
% 0.20/0.54    inference(backward_demodulation,[],[f236,f253])).
% 0.20/0.54  fof(f236,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) | (~spl6_10 | ~spl6_14)),
% 0.20/0.54    inference(backward_demodulation,[],[f211,f234])).
% 0.20/0.54  fof(f234,plain,(
% 0.20/0.54    k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) | ~spl6_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f232])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    spl6_14 <=> k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.54  fof(f211,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))) | ~spl6_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f209])).
% 0.20/0.54  fof(f209,plain,(
% 0.20/0.54    spl6_10 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.54  fof(f546,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | (spl6_2 | ~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(forward_demodulation,[],[f385,f485])).
% 0.20/0.54  fof(f385,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | (spl6_2 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f121,f360])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | spl6_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f119])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    spl6_2 <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.54  fof(f542,plain,(
% 0.20/0.54    spl6_3 | ~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f536])).
% 0.20/0.54  fof(f536,plain,(
% 0.20/0.54    $false | (spl6_3 | ~spl6_8 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(resolution,[],[f507,f506])).
% 0.20/0.54  fof(f506,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl6_3 | ~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f469,f485])).
% 0.20/0.54  fof(f469,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | (spl6_3 | ~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(forward_demodulation,[],[f462,f108])).
% 0.20/0.54  fof(f462,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (spl6_3 | ~spl6_8 | ~spl6_16 | ~spl6_24)),
% 0.20/0.54    inference(backward_demodulation,[],[f125,f457])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f123])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    spl6_3 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.54  fof(f456,plain,(
% 0.20/0.54    ~spl6_15 | spl6_23 | spl6_24),
% 0.20/0.54    inference(avatar_split_clause,[],[f405,f358,f354,f247])).
% 0.20/0.54  fof(f247,plain,(
% 0.20/0.54    spl6_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.54  fof(f354,plain,(
% 0.20/0.54    spl6_23 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.54  fof(f405,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    inference(resolution,[],[f59,f342])).
% 0.20/0.54  fof(f342,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f339])).
% 0.20/0.54  fof(f339,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~v1_funct_2(X5,X3,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.54    inference(superposition,[],[f288,f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.54  fof(f288,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X1,X2,X0) = X1 | k1_xboole_0 = X2 | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.54    inference(resolution,[],[f96,f100])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(definition_folding,[],[f38,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.20/0.54    inference(rectify,[],[f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f42])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  fof(f433,plain,(
% 0.20/0.54    spl6_3 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_23),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f432])).
% 0.20/0.54  fof(f432,plain,(
% 0.20/0.54    $false | (spl6_3 | ~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_23)),
% 0.20/0.54    inference(resolution,[],[f402,f125])).
% 0.20/0.54  fof(f402,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl6_10 | ~spl6_14 | ~spl6_16 | ~spl6_23)),
% 0.20/0.54    inference(backward_demodulation,[],[f259,f400])).
% 0.20/0.54  fof(f400,plain,(
% 0.20/0.54    sK1 = k1_relat_1(sK3) | (~spl6_14 | ~spl6_23)),
% 0.20/0.54    inference(backward_demodulation,[],[f234,f366])).
% 0.20/0.54  fof(f366,plain,(
% 0.20/0.54    sK1 = k2_relat_1(k2_funct_1(sK3)) | (~spl6_14 | ~spl6_23)),
% 0.20/0.54    inference(backward_demodulation,[],[f234,f356])).
% 0.20/0.54  fof(f356,plain,(
% 0.20/0.54    sK1 = k1_relat_1(sK3) | ~spl6_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f354])).
% 0.20/0.54  fof(f381,plain,(
% 0.20/0.54    spl6_2 | ~spl6_11 | ~spl6_14 | ~spl6_16 | ~spl6_23),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f379])).
% 0.20/0.54  fof(f379,plain,(
% 0.20/0.54    $false | (spl6_2 | ~spl6_11 | ~spl6_14 | ~spl6_16 | ~spl6_23)),
% 0.20/0.54    inference(resolution,[],[f365,f121])).
% 0.20/0.54  fof(f365,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | (~spl6_11 | ~spl6_14 | ~spl6_16 | ~spl6_23)),
% 0.20/0.54    inference(backward_demodulation,[],[f258,f356])).
% 0.20/0.54  fof(f258,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | (~spl6_11 | ~spl6_14 | ~spl6_16)),
% 0.20/0.54    inference(backward_demodulation,[],[f237,f253])).
% 0.20/0.54  fof(f237,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | (~spl6_11 | ~spl6_14)),
% 0.20/0.54    inference(backward_demodulation,[],[f216,f234])).
% 0.20/0.54  fof(f216,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~spl6_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f214])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    spl6_11 <=> v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.54  fof(f257,plain,(
% 0.20/0.54    spl6_15),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f256])).
% 0.20/0.54  fof(f256,plain,(
% 0.20/0.54    $false | spl6_15),
% 0.20/0.54    inference(resolution,[],[f249,f60])).
% 0.20/0.54  fof(f249,plain,(
% 0.20/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f247])).
% 0.20/0.54  fof(f255,plain,(
% 0.20/0.54    ~spl6_15 | spl6_16),
% 0.20/0.54    inference(avatar_split_clause,[],[f245,f251,f247])).
% 0.20/0.54  fof(f245,plain,(
% 0.20/0.54    sK2 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    inference(superposition,[],[f62,f95])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  fof(f235,plain,(
% 0.20/0.54    ~spl6_6 | ~spl6_7 | spl6_14),
% 0.20/0.54    inference(avatar_split_clause,[],[f230,f232,f149,f145])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    spl6_6 <=> v1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    spl6_7 <=> v1_funct_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.54    inference(resolution,[],[f81,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    v2_funct_1(sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.54  fof(f229,plain,(
% 0.20/0.54    ~spl6_6 | ~spl6_7 | spl6_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f227,f205,f149,f145])).
% 0.20/0.54  fof(f205,plain,(
% 0.20/0.54    spl6_9 <=> v1_relat_1(k2_funct_1(sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_9),
% 0.20/0.54    inference(resolution,[],[f207,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.54  fof(f207,plain,(
% 0.20/0.54    ~v1_relat_1(k2_funct_1(sK3)) | spl6_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f205])).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    ~spl6_9 | ~spl6_1 | spl6_11 | ~spl6_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f202,f197,f214,f115,f205])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    spl6_1 <=> v1_funct_1(k2_funct_1(sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.54  fof(f202,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl6_8),
% 0.20/0.54    inference(superposition,[],[f76,f199])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    ~spl6_9 | ~spl6_1 | spl6_10 | ~spl6_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f201,f197,f209,f115,f205])).
% 0.20/0.54  fof(f201,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl6_8),
% 0.20/0.54    inference(superposition,[],[f77,f199])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    ~spl6_6 | ~spl6_7 | spl6_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f195,f197,f149,f145])).
% 0.20/0.54  fof(f195,plain,(
% 0.20/0.54    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.54    inference(resolution,[],[f80,f61])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    spl6_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f159])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    $false | spl6_6),
% 0.20/0.54    inference(resolution,[],[f158,f60])).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_6),
% 0.20/0.54    inference(resolution,[],[f93,f147])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ~v1_relat_1(sK3) | spl6_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f145])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    spl6_7),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    $false | spl6_7),
% 0.20/0.54    inference(resolution,[],[f151,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    v1_funct_1(sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    ~v1_funct_1(sK3) | spl6_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f149])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ~spl6_6 | ~spl6_7 | spl6_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f143,f115,f149,f145])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_1),
% 0.20/0.54    inference(resolution,[],[f79,f117])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ~v1_funct_1(k2_funct_1(sK3)) | spl6_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f115])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f63,f123,f119,f115])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (32142)------------------------------
% 0.20/0.54  % (32142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32142)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (32142)Memory used [KB]: 6396
% 0.20/0.54  % (32142)Time elapsed: 0.134 s
% 0.20/0.54  % (32142)------------------------------
% 0.20/0.54  % (32142)------------------------------
% 0.20/0.54  % (32129)Success in time 0.187 s
%------------------------------------------------------------------------------
