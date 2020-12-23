%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:19 EST 2020

% Result     : Theorem 4.76s
% Output     : Refutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 543 expanded)
%              Number of leaves         :   31 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          :  574 (2944 expanded)
%              Number of equality atoms :   82 ( 580 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10561,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f134,f185,f236,f445,f660,f822,f823,f1038,f5356,f5396,f6900,f10557,f10559])).

fof(f10559,plain,
    ( spl4_2
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f10558])).

fof(f10558,plain,
    ( $false
    | spl4_2
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f10549,f4221])).

fof(f4221,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f4218,f201])).

fof(f201,plain,
    ( ! [X14] : v1_relat_1(k7_relat_1(sK3,X14))
    | ~ spl4_6 ),
    inference(resolution,[],[f142,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f142,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f4218,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_2
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(resolution,[],[f4212,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
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

fof(f4212,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_2
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(resolution,[],[f3575,f308])).

fof(f308,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f307,f63])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f55])).

fof(f55,plain,
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
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

fof(f307,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f300,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f300,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(superposition,[],[f120,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f120,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3575,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ v5_relat_1(k7_relat_1(sK3,sK2),X0) )
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3571,f201])).

fof(f3571,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ v5_relat_1(k7_relat_1(sK3,sK2),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(resolution,[],[f3540,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f3540,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X2) )
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f2008,f3529])).

fof(f3529,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(resolution,[],[f3511,f66])).

fof(f66,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f3511,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK0)
        | k1_relat_1(k7_relat_1(sK3,X3)) = X3 )
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f189,f364])).

fof(f364,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl4_22
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f189,plain,
    ( ! [X3] :
        ( k1_relat_1(k7_relat_1(sK3,X3)) = X3
        | ~ r1_tarski(X3,k1_relat_1(sK3)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f142,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f2008,plain,
    ( ! [X2] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X2)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2) )
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f2007,f182])).

fof(f182,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(subsumption_resolution,[],[f177,f63])).

fof(f177,plain,(
    ! [X0] :
      ( k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f65,f69])).

fof(f2007,plain,
    ( ! [X2] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X2)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2) )
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f277,f182])).

fof(f277,plain,
    ( ! [X2] :
        ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl4_16
  <=> ! [X2] :
        ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f10549,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(resolution,[],[f10534,f4888])).

fof(f4888,plain,
    ( ! [X15] :
        ( ~ v5_relat_1(k7_relat_1(sK3,sK2),X15)
        | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X15) )
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f4887,f182])).

fof(f4887,plain,
    ( ! [X15] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X15)
        | ~ v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),X15) )
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1056,f182])).

fof(f1056,plain,
    ( ! [X15] :
        ( r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X15)
        | ~ v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),X15) )
    | ~ spl4_14 ),
    inference(resolution,[],[f269,f104])).

fof(f269,plain,
    ( v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl4_14
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f10534,plain,
    ( ! [X9] : v5_relat_1(k7_relat_1(sK3,X9),sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f2917,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2917,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(resolution,[],[f2613,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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

fof(f2613,plain,
    ( ! [X6] : r1_tarski(k7_relat_1(sK3,X6),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f311,f195])).

fof(f195,plain,
    ( ! [X8] : r1_tarski(k7_relat_1(sK3,X8),sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f142,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f311,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK3)
      | r1_tarski(X1,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f179,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f179,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f65,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f10557,plain,
    ( spl4_3
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f10556])).

fof(f10556,plain,
    ( $false
    | spl4_3
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f10548,f337])).

fof(f337,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f336,f63])).

fof(f336,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f335,f65])).

fof(f335,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(superposition,[],[f124,f69])).

fof(f124,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f10548,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(resolution,[],[f10534,f3587])).

fof(f3587,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k7_relat_1(sK3,sK2),X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) )
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3583,f201])).

fof(f3583,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v5_relat_1(k7_relat_1(sK3,sK2),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(resolution,[],[f3539,f104])).

fof(f3539,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X3)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X3))) )
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f2070,f3529])).

fof(f2070,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X3)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X3))) )
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f2069,f182])).

fof(f2069,plain,
    ( ! [X3] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X3)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3) )
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f281,f182])).

fof(f281,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl4_17
  <=> ! [X3] :
        ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f6900,plain,
    ( ~ spl4_11
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f6899])).

fof(f6899,plain,
    ( $false
    | ~ spl4_11
    | spl4_22 ),
    inference(subsumption_resolution,[],[f363,f1422])).

fof(f1422,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f174,f170])).

fof(f170,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f174,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f65,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f363,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f362])).

fof(f5396,plain,
    ( spl4_4
    | spl4_11 ),
    inference(avatar_split_clause,[],[f5395,f168,f127])).

fof(f127,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f5395,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f751,f65])).

fof(f751,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f64,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
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
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f64,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f5356,plain,
    ( ~ spl4_21
    | spl4_22
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5355,f141,f362,f358])).

fof(f358,plain,
    ( spl4_21
  <=> r1_tarski(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f5355,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3))
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f942,f142])).

fof(f942,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(superposition,[],[f82,f211])).

fof(f211,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f209,f142])).

fof(f209,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f172,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f172,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f65,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1038,plain,
    ( ~ spl4_6
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f1037])).

fof(f1037,plain,
    ( $false
    | ~ spl4_6
    | spl4_14 ),
    inference(subsumption_resolution,[],[f1036,f63])).

fof(f1036,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl4_6
    | spl4_14 ),
    inference(subsumption_resolution,[],[f1035,f65])).

fof(f1035,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | spl4_14 ),
    inference(subsumption_resolution,[],[f1034,f201])).

fof(f1034,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_14 ),
    inference(superposition,[],[f270,f69])).

fof(f270,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f268])).

fof(f823,plain,
    ( ~ spl4_14
    | spl4_17
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f818,f114,f280,f268])).

fof(f114,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f818,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f115,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f115,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f822,plain,
    ( ~ spl4_14
    | spl4_16
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f817,f114,f276,f268])).

fof(f817,plain,
    ( ! [X2] :
        ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f115,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f660,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f656,f145,f141])).

fof(f145,plain,
    ( spl4_7
  <=> ! [X1] : v1_funct_1(k7_relat_1(sK3,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f656,plain,(
    ! [X1] :
      ( v1_funct_1(k7_relat_1(sK3,X1))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f63,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f445,plain,
    ( ~ spl4_5
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | ~ spl4_5
    | spl4_21 ),
    inference(subsumption_resolution,[],[f442,f85])).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f442,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | spl4_21 ),
    inference(backward_demodulation,[],[f360,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f360,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f358])).

fof(f236,plain,
    ( spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f214,f146])).

fof(f146,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK3,X1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f145])).

fof(f214,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f213,f63])).

fof(f213,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f212,f65])).

fof(f212,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(superposition,[],[f116,f69])).

fof(f116,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f185,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f183,f100])).

fof(f100,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f183,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f178,f143])).

fof(f143,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f178,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f65,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f134,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f67,f131,f127])).

fof(f67,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f125,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f68,f122,f118,f114])).

fof(f68,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31903)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (31905)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (31897)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (31895)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (31891)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (31899)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (31893)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (31894)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (31904)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (31898)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (31911)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (31909)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (31896)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (31892)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31902)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (31907)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (31910)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (31894)Refutation not found, incomplete strategy% (31894)------------------------------
% 0.20/0.52  % (31894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31894)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31894)Memory used [KB]: 10746
% 0.20/0.52  % (31894)Time elapsed: 0.095 s
% 0.20/0.52  % (31894)------------------------------
% 0.20/0.52  % (31894)------------------------------
% 0.20/0.52  % (31901)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (31900)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.54  % (31906)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.54  % (31908)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 4.03/0.90  % (31901)Time limit reached!
% 4.03/0.90  % (31901)------------------------------
% 4.03/0.90  % (31901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.90  % (31901)Termination reason: Time limit
% 4.03/0.90  % (31901)Termination phase: Saturation
% 4.03/0.90  
% 4.03/0.90  % (31901)Memory used [KB]: 9083
% 4.03/0.90  % (31901)Time elapsed: 0.500 s
% 4.03/0.90  % (31901)------------------------------
% 4.03/0.90  % (31901)------------------------------
% 4.03/0.90  % (31892)Time limit reached!
% 4.03/0.90  % (31892)------------------------------
% 4.03/0.90  % (31892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (31891)Time limit reached!
% 4.03/0.91  % (31891)------------------------------
% 4.03/0.91  % (31891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (31891)Termination reason: Time limit
% 4.03/0.91  % (31891)Termination phase: Saturation
% 4.03/0.91  
% 4.03/0.91  % (31891)Memory used [KB]: 14072
% 4.03/0.91  % (31891)Time elapsed: 0.500 s
% 4.03/0.91  % (31891)------------------------------
% 4.03/0.91  % (31891)------------------------------
% 4.03/0.91  % (31903)Time limit reached!
% 4.03/0.91  % (31903)------------------------------
% 4.03/0.91  % (31903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (31903)Termination reason: Time limit
% 4.03/0.91  % (31903)Termination phase: Saturation
% 4.03/0.91  
% 4.03/0.91  % (31903)Memory used [KB]: 12537
% 4.03/0.91  % (31903)Time elapsed: 0.500 s
% 4.03/0.91  % (31903)------------------------------
% 4.03/0.91  % (31903)------------------------------
% 4.03/0.92  % (31892)Termination reason: Time limit
% 4.03/0.92  
% 4.03/0.92  % (31892)Memory used [KB]: 12792
% 4.03/0.92  % (31892)Time elapsed: 0.503 s
% 4.03/0.92  % (31892)------------------------------
% 4.03/0.92  % (31892)------------------------------
% 4.76/0.98  % (31896)Time limit reached!
% 4.76/0.98  % (31896)------------------------------
% 4.76/0.98  % (31896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/0.98  % (31896)Termination reason: Time limit
% 4.76/0.98  
% 4.76/0.98  % (31896)Memory used [KB]: 12920
% 4.76/0.98  % (31896)Time elapsed: 0.529 s
% 4.76/0.98  % (31896)------------------------------
% 4.76/0.98  % (31896)------------------------------
% 4.76/0.98  % (31910)Refutation found. Thanks to Tanya!
% 4.76/0.98  % SZS status Theorem for theBenchmark
% 4.76/0.99  % SZS output start Proof for theBenchmark
% 4.76/1.00  fof(f10561,plain,(
% 4.76/1.00    $false),
% 4.76/1.00    inference(avatar_sat_refutation,[],[f125,f134,f185,f236,f445,f660,f822,f823,f1038,f5356,f5396,f6900,f10557,f10559])).
% 4.76/1.00  fof(f10559,plain,(
% 4.76/1.00    spl4_2 | ~spl4_6 | ~spl4_14 | ~spl4_16 | ~spl4_22),
% 4.76/1.00    inference(avatar_contradiction_clause,[],[f10558])).
% 4.76/1.00  fof(f10558,plain,(
% 4.76/1.00    $false | (spl4_2 | ~spl4_6 | ~spl4_14 | ~spl4_16 | ~spl4_22)),
% 4.76/1.00    inference(subsumption_resolution,[],[f10549,f4221])).
% 4.76/1.00  fof(f4221,plain,(
% 4.76/1.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl4_2 | ~spl4_6 | ~spl4_16 | ~spl4_22)),
% 4.76/1.00    inference(subsumption_resolution,[],[f4218,f201])).
% 4.76/1.00  fof(f201,plain,(
% 4.76/1.00    ( ! [X14] : (v1_relat_1(k7_relat_1(sK3,X14))) ) | ~spl4_6),
% 4.76/1.00    inference(resolution,[],[f142,f103])).
% 4.76/1.00  fof(f103,plain,(
% 4.76/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f53])).
% 4.76/1.00  fof(f53,plain,(
% 4.76/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.76/1.00    inference(ennf_transformation,[],[f9])).
% 4.76/1.00  fof(f9,axiom,(
% 4.76/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.76/1.00  fof(f142,plain,(
% 4.76/1.00    v1_relat_1(sK3) | ~spl4_6),
% 4.76/1.00    inference(avatar_component_clause,[],[f141])).
% 4.76/1.00  fof(f141,plain,(
% 4.76/1.00    spl4_6 <=> v1_relat_1(sK3)),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 4.76/1.00  fof(f4218,plain,(
% 4.76/1.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | (spl4_2 | ~spl4_6 | ~spl4_16 | ~spl4_22)),
% 4.76/1.00    inference(resolution,[],[f4212,f105])).
% 4.76/1.00  fof(f105,plain,(
% 4.76/1.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f62])).
% 4.76/1.00  fof(f62,plain,(
% 4.76/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.76/1.00    inference(nnf_transformation,[],[f54])).
% 4.76/1.00  fof(f54,plain,(
% 4.76/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.76/1.00    inference(ennf_transformation,[],[f8])).
% 4.76/1.00  fof(f8,axiom,(
% 4.76/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 4.76/1.00  fof(f4212,plain,(
% 4.76/1.00    ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | (spl4_2 | ~spl4_6 | ~spl4_16 | ~spl4_22)),
% 4.76/1.00    inference(resolution,[],[f3575,f308])).
% 4.76/1.00  fof(f308,plain,(
% 4.76/1.00    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 4.76/1.00    inference(subsumption_resolution,[],[f307,f63])).
% 4.76/1.00  fof(f63,plain,(
% 4.76/1.00    v1_funct_1(sK3)),
% 4.76/1.00    inference(cnf_transformation,[],[f56])).
% 4.76/1.00  fof(f56,plain,(
% 4.76/1.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 4.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f55])).
% 4.76/1.00  fof(f55,plain,(
% 4.76/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 4.76/1.00    introduced(choice_axiom,[])).
% 4.76/1.00  fof(f27,plain,(
% 4.76/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 4.76/1.00    inference(flattening,[],[f26])).
% 4.76/1.00  fof(f26,plain,(
% 4.76/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 4.76/1.00    inference(ennf_transformation,[],[f25])).
% 4.76/1.00  fof(f25,negated_conjecture,(
% 4.76/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 4.76/1.00    inference(negated_conjecture,[],[f24])).
% 4.76/1.00  fof(f24,conjecture,(
% 4.76/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 4.76/1.00  fof(f307,plain,(
% 4.76/1.00    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(sK3) | spl4_2),
% 4.76/1.00    inference(subsumption_resolution,[],[f300,f65])).
% 4.76/1.00  fof(f65,plain,(
% 4.76/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.76/1.00    inference(cnf_transformation,[],[f56])).
% 4.76/1.00  fof(f300,plain,(
% 4.76/1.00    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_2),
% 4.76/1.00    inference(superposition,[],[f120,f69])).
% 4.76/1.00  fof(f69,plain,(
% 4.76/1.00    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f29])).
% 4.76/1.00  fof(f29,plain,(
% 4.76/1.00    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.76/1.00    inference(flattening,[],[f28])).
% 4.76/1.00  fof(f28,plain,(
% 4.76/1.00    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.76/1.00    inference(ennf_transformation,[],[f22])).
% 4.76/1.00  fof(f22,axiom,(
% 4.76/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 4.76/1.00  fof(f120,plain,(
% 4.76/1.00    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 4.76/1.00    inference(avatar_component_clause,[],[f118])).
% 4.76/1.00  fof(f118,plain,(
% 4.76/1.00    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 4.76/1.00  fof(f3575,plain,(
% 4.76/1.00    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~v5_relat_1(k7_relat_1(sK3,sK2),X0)) ) | (~spl4_6 | ~spl4_16 | ~spl4_22)),
% 4.76/1.00    inference(subsumption_resolution,[],[f3571,f201])).
% 4.76/1.00  fof(f3571,plain,(
% 4.76/1.00    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~v5_relat_1(k7_relat_1(sK3,sK2),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | (~spl4_6 | ~spl4_16 | ~spl4_22)),
% 4.76/1.00    inference(resolution,[],[f3540,f104])).
% 4.76/1.00  fof(f104,plain,(
% 4.76/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f62])).
% 4.76/1.00  fof(f3540,plain,(
% 4.76/1.00    ( ! [X2] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X2)) ) | (~spl4_6 | ~spl4_16 | ~spl4_22)),
% 4.76/1.00    inference(backward_demodulation,[],[f2008,f3529])).
% 4.76/1.00  fof(f3529,plain,(
% 4.76/1.00    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_6 | ~spl4_22)),
% 4.76/1.00    inference(resolution,[],[f3511,f66])).
% 4.76/1.00  fof(f66,plain,(
% 4.76/1.00    r1_tarski(sK2,sK0)),
% 4.76/1.00    inference(cnf_transformation,[],[f56])).
% 4.76/1.00  fof(f3511,plain,(
% 4.76/1.00    ( ! [X3] : (~r1_tarski(X3,sK0) | k1_relat_1(k7_relat_1(sK3,X3)) = X3) ) | (~spl4_6 | ~spl4_22)),
% 4.76/1.00    inference(forward_demodulation,[],[f189,f364])).
% 4.76/1.00  fof(f364,plain,(
% 4.76/1.00    sK0 = k1_relat_1(sK3) | ~spl4_22),
% 4.76/1.00    inference(avatar_component_clause,[],[f362])).
% 4.76/1.00  fof(f362,plain,(
% 4.76/1.00    spl4_22 <=> sK0 = k1_relat_1(sK3)),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 4.76/1.00  fof(f189,plain,(
% 4.76/1.00    ( ! [X3] : (k1_relat_1(k7_relat_1(sK3,X3)) = X3 | ~r1_tarski(X3,k1_relat_1(sK3))) ) | ~spl4_6),
% 4.76/1.00    inference(resolution,[],[f142,f82])).
% 4.76/1.00  fof(f82,plain,(
% 4.76/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f38])).
% 4.76/1.00  fof(f38,plain,(
% 4.76/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.76/1.00    inference(flattening,[],[f37])).
% 4.76/1.00  fof(f37,plain,(
% 4.76/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.76/1.00    inference(ennf_transformation,[],[f16])).
% 4.76/1.00  fof(f16,axiom,(
% 4.76/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 4.76/1.00  fof(f2008,plain,(
% 4.76/1.00    ( ! [X2] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X2) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X2)) ) | ~spl4_16),
% 4.76/1.00    inference(forward_demodulation,[],[f2007,f182])).
% 4.76/1.00  fof(f182,plain,(
% 4.76/1.00    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) )),
% 4.76/1.00    inference(subsumption_resolution,[],[f177,f63])).
% 4.76/1.00  fof(f177,plain,(
% 4.76/1.00    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) | ~v1_funct_1(sK3)) )),
% 4.76/1.00    inference(resolution,[],[f65,f69])).
% 4.76/1.00  fof(f2007,plain,(
% 4.76/1.00    ( ! [X2] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X2) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2)) ) | ~spl4_16),
% 4.76/1.00    inference(forward_demodulation,[],[f277,f182])).
% 4.76/1.00  fof(f277,plain,(
% 4.76/1.00    ( ! [X2] : (v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2)) ) | ~spl4_16),
% 4.76/1.00    inference(avatar_component_clause,[],[f276])).
% 4.76/1.00  fof(f276,plain,(
% 4.76/1.00    spl4_16 <=> ! [X2] : (v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2))),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 4.76/1.00  fof(f10549,plain,(
% 4.76/1.00    r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (~spl4_6 | ~spl4_14)),
% 4.76/1.00    inference(resolution,[],[f10534,f4888])).
% 4.76/1.00  fof(f4888,plain,(
% 4.76/1.00    ( ! [X15] : (~v5_relat_1(k7_relat_1(sK3,sK2),X15) | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X15)) ) | ~spl4_14),
% 4.76/1.00    inference(forward_demodulation,[],[f4887,f182])).
% 4.76/1.00  fof(f4887,plain,(
% 4.76/1.00    ( ! [X15] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X15) | ~v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),X15)) ) | ~spl4_14),
% 4.76/1.00    inference(forward_demodulation,[],[f1056,f182])).
% 4.76/1.00  fof(f1056,plain,(
% 4.76/1.00    ( ! [X15] : (r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X15) | ~v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),X15)) ) | ~spl4_14),
% 4.76/1.00    inference(resolution,[],[f269,f104])).
% 4.76/1.00  fof(f269,plain,(
% 4.76/1.00    v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_14),
% 4.76/1.00    inference(avatar_component_clause,[],[f268])).
% 4.76/1.00  fof(f268,plain,(
% 4.76/1.00    spl4_14 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 4.76/1.00  fof(f10534,plain,(
% 4.76/1.00    ( ! [X9] : (v5_relat_1(k7_relat_1(sK3,X9),sK1)) ) | ~spl4_6),
% 4.76/1.00    inference(resolution,[],[f2917,f95])).
% 4.76/1.00  fof(f95,plain,(
% 4.76/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.76/1.00    inference(cnf_transformation,[],[f47])).
% 4.76/1.00  fof(f47,plain,(
% 4.76/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.76/1.00    inference(ennf_transformation,[],[f19])).
% 4.76/1.00  fof(f19,axiom,(
% 4.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 4.76/1.00  fof(f2917,plain,(
% 4.76/1.00    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_6),
% 4.76/1.00    inference(resolution,[],[f2613,f88])).
% 4.76/1.00  fof(f88,plain,(
% 4.76/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f60])).
% 4.76/1.00  fof(f60,plain,(
% 4.76/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.76/1.00    inference(nnf_transformation,[],[f5])).
% 4.76/1.00  fof(f5,axiom,(
% 4.76/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 4.76/1.00  fof(f2613,plain,(
% 4.76/1.00    ( ! [X6] : (r1_tarski(k7_relat_1(sK3,X6),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_6),
% 4.76/1.00    inference(resolution,[],[f311,f195])).
% 4.76/1.00  fof(f195,plain,(
% 4.76/1.00    ( ! [X8] : (r1_tarski(k7_relat_1(sK3,X8),sK3)) ) | ~spl4_6),
% 4.76/1.00    inference(resolution,[],[f142,f93])).
% 4.76/1.00  fof(f93,plain,(
% 4.76/1.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f46])).
% 4.76/1.00  fof(f46,plain,(
% 4.76/1.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 4.76/1.00    inference(ennf_transformation,[],[f14])).
% 4.76/1.00  fof(f14,axiom,(
% 4.76/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 4.76/1.00  fof(f311,plain,(
% 4.76/1.00    ( ! [X1] : (~r1_tarski(X1,sK3) | r1_tarski(X1,k2_zfmisc_1(sK0,sK1))) )),
% 4.76/1.00    inference(resolution,[],[f179,f86])).
% 4.76/1.00  fof(f86,plain,(
% 4.76/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f42])).
% 4.76/1.00  fof(f42,plain,(
% 4.76/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.76/1.00    inference(flattening,[],[f41])).
% 4.76/1.00  fof(f41,plain,(
% 4.76/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.76/1.00    inference(ennf_transformation,[],[f1])).
% 4.76/1.00  fof(f1,axiom,(
% 4.76/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.76/1.00  fof(f179,plain,(
% 4.76/1.00    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 4.76/1.00    inference(resolution,[],[f65,f87])).
% 4.76/1.00  fof(f87,plain,(
% 4.76/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.76/1.00    inference(cnf_transformation,[],[f60])).
% 4.76/1.00  fof(f10557,plain,(
% 4.76/1.00    spl4_3 | ~spl4_6 | ~spl4_17 | ~spl4_22),
% 4.76/1.00    inference(avatar_contradiction_clause,[],[f10556])).
% 4.76/1.00  fof(f10556,plain,(
% 4.76/1.00    $false | (spl4_3 | ~spl4_6 | ~spl4_17 | ~spl4_22)),
% 4.76/1.00    inference(subsumption_resolution,[],[f10548,f337])).
% 4.76/1.00  fof(f337,plain,(
% 4.76/1.00    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 4.76/1.00    inference(subsumption_resolution,[],[f336,f63])).
% 4.76/1.00  fof(f336,plain,(
% 4.76/1.00    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 4.76/1.00    inference(subsumption_resolution,[],[f335,f65])).
% 4.76/1.00  fof(f335,plain,(
% 4.76/1.00    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 4.76/1.00    inference(superposition,[],[f124,f69])).
% 4.76/1.00  fof(f124,plain,(
% 4.76/1.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 4.76/1.00    inference(avatar_component_clause,[],[f122])).
% 4.76/1.00  fof(f122,plain,(
% 4.76/1.00    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 4.76/1.00  fof(f10548,plain,(
% 4.76/1.00    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_6 | ~spl4_17 | ~spl4_22)),
% 4.76/1.00    inference(resolution,[],[f10534,f3587])).
% 4.76/1.00  fof(f3587,plain,(
% 4.76/1.00    ( ! [X0] : (~v5_relat_1(k7_relat_1(sK3,sK2),X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | (~spl4_6 | ~spl4_17 | ~spl4_22)),
% 4.76/1.00    inference(subsumption_resolution,[],[f3583,f201])).
% 4.76/1.00  fof(f3583,plain,(
% 4.76/1.00    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v5_relat_1(k7_relat_1(sK3,sK2),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | (~spl4_6 | ~spl4_17 | ~spl4_22)),
% 4.76/1.00    inference(resolution,[],[f3539,f104])).
% 4.76/1.00  fof(f3539,plain,(
% 4.76/1.00    ( ! [X3] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X3) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))) ) | (~spl4_6 | ~spl4_17 | ~spl4_22)),
% 4.76/1.00    inference(backward_demodulation,[],[f2070,f3529])).
% 4.76/1.00  fof(f2070,plain,(
% 4.76/1.00    ( ! [X3] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X3) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X3)))) ) | ~spl4_17),
% 4.76/1.00    inference(forward_demodulation,[],[f2069,f182])).
% 4.76/1.00  fof(f2069,plain,(
% 4.76/1.00    ( ! [X3] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X3))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3)) ) | ~spl4_17),
% 4.76/1.00    inference(forward_demodulation,[],[f281,f182])).
% 4.76/1.00  fof(f281,plain,(
% 4.76/1.00    ( ! [X3] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3)) ) | ~spl4_17),
% 4.76/1.00    inference(avatar_component_clause,[],[f280])).
% 4.76/1.00  fof(f280,plain,(
% 4.76/1.00    spl4_17 <=> ! [X3] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3))),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 4.76/1.00  fof(f6900,plain,(
% 4.76/1.00    ~spl4_11 | spl4_22),
% 4.76/1.00    inference(avatar_contradiction_clause,[],[f6899])).
% 4.76/1.00  fof(f6899,plain,(
% 4.76/1.00    $false | (~spl4_11 | spl4_22)),
% 4.76/1.00    inference(subsumption_resolution,[],[f363,f1422])).
% 4.76/1.00  fof(f1422,plain,(
% 4.76/1.00    sK0 = k1_relat_1(sK3) | ~spl4_11),
% 4.76/1.00    inference(forward_demodulation,[],[f174,f170])).
% 4.76/1.00  fof(f170,plain,(
% 4.76/1.00    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_11),
% 4.76/1.00    inference(avatar_component_clause,[],[f168])).
% 4.76/1.00  fof(f168,plain,(
% 4.76/1.00    spl4_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 4.76/1.00  fof(f174,plain,(
% 4.76/1.00    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 4.76/1.00    inference(resolution,[],[f65,f76])).
% 4.76/1.00  fof(f76,plain,(
% 4.76/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.76/1.00    inference(cnf_transformation,[],[f32])).
% 4.76/1.00  fof(f32,plain,(
% 4.76/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.76/1.00    inference(ennf_transformation,[],[f20])).
% 4.76/1.00  fof(f20,axiom,(
% 4.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 4.76/1.00  fof(f363,plain,(
% 4.76/1.00    sK0 != k1_relat_1(sK3) | spl4_22),
% 4.76/1.00    inference(avatar_component_clause,[],[f362])).
% 4.76/1.00  fof(f5396,plain,(
% 4.76/1.00    spl4_4 | spl4_11),
% 4.76/1.00    inference(avatar_split_clause,[],[f5395,f168,f127])).
% 4.76/1.00  fof(f127,plain,(
% 4.76/1.00    spl4_4 <=> k1_xboole_0 = sK1),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 4.76/1.00  fof(f5395,plain,(
% 4.76/1.00    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 4.76/1.00    inference(subsumption_resolution,[],[f751,f65])).
% 4.76/1.00  fof(f751,plain,(
% 4.76/1.00    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.76/1.00    inference(resolution,[],[f64,f70])).
% 4.76/1.00  fof(f70,plain,(
% 4.76/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.76/1.00    inference(cnf_transformation,[],[f57])).
% 4.76/1.00  fof(f57,plain,(
% 4.76/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.76/1.00    inference(nnf_transformation,[],[f31])).
% 4.76/1.00  fof(f31,plain,(
% 4.76/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.76/1.00    inference(flattening,[],[f30])).
% 4.76/1.00  fof(f30,plain,(
% 4.76/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.76/1.00    inference(ennf_transformation,[],[f21])).
% 4.76/1.00  fof(f21,axiom,(
% 4.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 4.76/1.00  fof(f64,plain,(
% 4.76/1.00    v1_funct_2(sK3,sK0,sK1)),
% 4.76/1.00    inference(cnf_transformation,[],[f56])).
% 4.76/1.00  fof(f5356,plain,(
% 4.76/1.00    ~spl4_21 | spl4_22 | ~spl4_6),
% 4.76/1.00    inference(avatar_split_clause,[],[f5355,f141,f362,f358])).
% 4.76/1.00  fof(f358,plain,(
% 4.76/1.00    spl4_21 <=> r1_tarski(sK0,k1_relat_1(sK3))),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 4.76/1.00  fof(f5355,plain,(
% 4.76/1.00    sK0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3)) | ~spl4_6),
% 4.76/1.00    inference(subsumption_resolution,[],[f942,f142])).
% 4.76/1.00  fof(f942,plain,(
% 4.76/1.00    sK0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_6),
% 4.76/1.00    inference(superposition,[],[f82,f211])).
% 4.76/1.00  fof(f211,plain,(
% 4.76/1.00    sK3 = k7_relat_1(sK3,sK0) | ~spl4_6),
% 4.76/1.00    inference(subsumption_resolution,[],[f209,f142])).
% 4.76/1.00  fof(f209,plain,(
% 4.76/1.00    sK3 = k7_relat_1(sK3,sK0) | ~v1_relat_1(sK3)),
% 4.76/1.00    inference(resolution,[],[f172,f81])).
% 4.76/1.00  fof(f81,plain,(
% 4.76/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f36])).
% 4.76/1.00  fof(f36,plain,(
% 4.76/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.76/1.00    inference(flattening,[],[f35])).
% 4.76/1.00  fof(f35,plain,(
% 4.76/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.76/1.00    inference(ennf_transformation,[],[f12])).
% 4.76/1.00  fof(f12,axiom,(
% 4.76/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 4.76/1.00  fof(f172,plain,(
% 4.76/1.00    v4_relat_1(sK3,sK0)),
% 4.76/1.00    inference(resolution,[],[f65,f94])).
% 4.76/1.00  fof(f94,plain,(
% 4.76/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.76/1.00    inference(cnf_transformation,[],[f47])).
% 4.76/1.00  fof(f1038,plain,(
% 4.76/1.00    ~spl4_6 | spl4_14),
% 4.76/1.00    inference(avatar_contradiction_clause,[],[f1037])).
% 4.76/1.00  fof(f1037,plain,(
% 4.76/1.00    $false | (~spl4_6 | spl4_14)),
% 4.76/1.00    inference(subsumption_resolution,[],[f1036,f63])).
% 4.76/1.00  fof(f1036,plain,(
% 4.76/1.00    ~v1_funct_1(sK3) | (~spl4_6 | spl4_14)),
% 4.76/1.00    inference(subsumption_resolution,[],[f1035,f65])).
% 4.76/1.00  fof(f1035,plain,(
% 4.76/1.00    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (~spl4_6 | spl4_14)),
% 4.76/1.00    inference(subsumption_resolution,[],[f1034,f201])).
% 4.76/1.00  fof(f1034,plain,(
% 4.76/1.00    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_14),
% 4.76/1.00    inference(superposition,[],[f270,f69])).
% 4.76/1.00  fof(f270,plain,(
% 4.76/1.00    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_14),
% 4.76/1.00    inference(avatar_component_clause,[],[f268])).
% 4.76/1.00  fof(f823,plain,(
% 4.76/1.00    ~spl4_14 | spl4_17 | ~spl4_1),
% 4.76/1.00    inference(avatar_split_clause,[],[f818,f114,f280,f268])).
% 4.76/1.00  fof(f114,plain,(
% 4.76/1.00    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 4.76/1.00  fof(f818,plain,(
% 4.76/1.00    ( ! [X3] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X3) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | ~spl4_1),
% 4.76/1.00    inference(resolution,[],[f115,f98])).
% 4.76/1.00  fof(f98,plain,(
% 4.76/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f49])).
% 4.76/1.00  fof(f49,plain,(
% 4.76/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.76/1.00    inference(flattening,[],[f48])).
% 4.76/1.00  fof(f48,plain,(
% 4.76/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.76/1.00    inference(ennf_transformation,[],[f23])).
% 4.76/1.00  fof(f23,axiom,(
% 4.76/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 4.76/1.00  fof(f115,plain,(
% 4.76/1.00    v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_1),
% 4.76/1.00    inference(avatar_component_clause,[],[f114])).
% 4.76/1.00  fof(f822,plain,(
% 4.76/1.00    ~spl4_14 | spl4_16 | ~spl4_1),
% 4.76/1.00    inference(avatar_split_clause,[],[f817,f114,f276,f268])).
% 4.76/1.00  fof(f817,plain,(
% 4.76/1.00    ( ! [X2] : (v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X2) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | ~spl4_1),
% 4.76/1.00    inference(resolution,[],[f115,f97])).
% 4.76/1.00  fof(f97,plain,(
% 4.76/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f49])).
% 4.76/1.00  fof(f660,plain,(
% 4.76/1.00    ~spl4_6 | spl4_7),
% 4.76/1.00    inference(avatar_split_clause,[],[f656,f145,f141])).
% 4.76/1.00  fof(f145,plain,(
% 4.76/1.00    spl4_7 <=> ! [X1] : v1_funct_1(k7_relat_1(sK3,X1))),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 4.76/1.00  fof(f656,plain,(
% 4.76/1.00    ( ! [X1] : (v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(sK3)) )),
% 4.76/1.00    inference(resolution,[],[f63,f102])).
% 4.76/1.00  fof(f102,plain,(
% 4.76/1.00    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f52])).
% 4.76/1.00  fof(f52,plain,(
% 4.76/1.00    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.76/1.00    inference(flattening,[],[f51])).
% 4.76/1.00  fof(f51,plain,(
% 4.76/1.00    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.76/1.00    inference(ennf_transformation,[],[f18])).
% 4.76/1.00  fof(f18,axiom,(
% 4.76/1.00    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 4.76/1.00  fof(f445,plain,(
% 4.76/1.00    ~spl4_5 | spl4_21),
% 4.76/1.00    inference(avatar_contradiction_clause,[],[f444])).
% 4.76/1.00  fof(f444,plain,(
% 4.76/1.00    $false | (~spl4_5 | spl4_21)),
% 4.76/1.00    inference(subsumption_resolution,[],[f442,f85])).
% 4.76/1.00  fof(f85,plain,(
% 4.76/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f2])).
% 4.76/1.00  fof(f2,axiom,(
% 4.76/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.76/1.00  fof(f442,plain,(
% 4.76/1.00    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | spl4_21)),
% 4.76/1.00    inference(backward_demodulation,[],[f360,f133])).
% 4.76/1.00  fof(f133,plain,(
% 4.76/1.00    k1_xboole_0 = sK0 | ~spl4_5),
% 4.76/1.00    inference(avatar_component_clause,[],[f131])).
% 4.76/1.00  fof(f131,plain,(
% 4.76/1.00    spl4_5 <=> k1_xboole_0 = sK0),
% 4.76/1.00    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 4.76/1.00  fof(f360,plain,(
% 4.76/1.00    ~r1_tarski(sK0,k1_relat_1(sK3)) | spl4_21),
% 4.76/1.00    inference(avatar_component_clause,[],[f358])).
% 4.76/1.00  fof(f236,plain,(
% 4.76/1.00    spl4_1 | ~spl4_7),
% 4.76/1.00    inference(avatar_contradiction_clause,[],[f235])).
% 4.76/1.00  fof(f235,plain,(
% 4.76/1.00    $false | (spl4_1 | ~spl4_7)),
% 4.76/1.00    inference(subsumption_resolution,[],[f214,f146])).
% 4.76/1.00  fof(f146,plain,(
% 4.76/1.00    ( ! [X1] : (v1_funct_1(k7_relat_1(sK3,X1))) ) | ~spl4_7),
% 4.76/1.00    inference(avatar_component_clause,[],[f145])).
% 4.76/1.00  fof(f214,plain,(
% 4.76/1.00    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl4_1),
% 4.76/1.00    inference(subsumption_resolution,[],[f213,f63])).
% 4.76/1.00  fof(f213,plain,(
% 4.76/1.00    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | spl4_1),
% 4.76/1.00    inference(subsumption_resolution,[],[f212,f65])).
% 4.76/1.00  fof(f212,plain,(
% 4.76/1.00    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_1),
% 4.76/1.00    inference(superposition,[],[f116,f69])).
% 4.76/1.00  fof(f116,plain,(
% 4.76/1.00    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 4.76/1.00    inference(avatar_component_clause,[],[f114])).
% 4.76/1.00  fof(f185,plain,(
% 4.76/1.00    spl4_6),
% 4.76/1.00    inference(avatar_contradiction_clause,[],[f184])).
% 4.76/1.00  fof(f184,plain,(
% 4.76/1.00    $false | spl4_6),
% 4.76/1.00    inference(subsumption_resolution,[],[f183,f100])).
% 4.76/1.00  fof(f100,plain,(
% 4.76/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.76/1.00    inference(cnf_transformation,[],[f10])).
% 4.76/1.00  fof(f10,axiom,(
% 4.76/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 4.76/1.00  fof(f183,plain,(
% 4.76/1.00    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_6),
% 4.76/1.00    inference(subsumption_resolution,[],[f178,f143])).
% 4.76/1.00  fof(f143,plain,(
% 4.76/1.00    ~v1_relat_1(sK3) | spl4_6),
% 4.76/1.00    inference(avatar_component_clause,[],[f141])).
% 4.76/1.00  fof(f178,plain,(
% 4.76/1.00    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 4.76/1.00    inference(resolution,[],[f65,f99])).
% 4.76/1.00  fof(f99,plain,(
% 4.76/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.76/1.00    inference(cnf_transformation,[],[f50])).
% 4.76/1.00  fof(f50,plain,(
% 4.76/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.76/1.00    inference(ennf_transformation,[],[f6])).
% 4.76/1.00  fof(f6,axiom,(
% 4.76/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 4.76/1.00  fof(f134,plain,(
% 4.76/1.00    ~spl4_4 | spl4_5),
% 4.76/1.00    inference(avatar_split_clause,[],[f67,f131,f127])).
% 4.76/1.00  fof(f67,plain,(
% 4.76/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 4.76/1.00    inference(cnf_transformation,[],[f56])).
% 4.76/1.00  fof(f125,plain,(
% 4.76/1.00    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 4.76/1.00    inference(avatar_split_clause,[],[f68,f122,f118,f114])).
% 4.76/1.00  fof(f68,plain,(
% 4.76/1.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 4.76/1.00    inference(cnf_transformation,[],[f56])).
% 4.76/1.00  % SZS output end Proof for theBenchmark
% 4.76/1.00  % (31910)------------------------------
% 4.76/1.00  % (31910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/1.00  % (31910)Termination reason: Refutation
% 4.76/1.00  
% 4.76/1.00  % (31910)Memory used [KB]: 9850
% 4.76/1.00  % (31910)Time elapsed: 0.544 s
% 4.76/1.00  % (31910)------------------------------
% 4.76/1.00  % (31910)------------------------------
% 4.76/1.00  % (31890)Success in time 0.644 s
%------------------------------------------------------------------------------
