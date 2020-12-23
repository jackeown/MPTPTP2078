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
% DateTime   : Thu Dec  3 13:03:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 737 expanded)
%              Number of leaves         :   25 ( 197 expanded)
%              Depth                    :   16
%              Number of atoms          :  544 (4195 expanded)
%              Number of equality atoms :  123 (1028 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f579,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f99,f115,f143,f198,f204,f233,f239,f273,f315,f332,f371,f375,f485,f544,f547,f549,f578])).

fof(f578,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl4_10 ),
    inference(resolution,[],[f193,f132])).

fof(f132,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f129,f130])).

fof(f130,plain,(
    ! [X2] : k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) ),
    inference(subsumption_resolution,[],[f121,f41])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f34])).

fof(f34,plain,
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f121,plain,(
    ! [X2] :
      ( k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f129,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f120,f41])).

fof(f120,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f43,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f193,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl4_10
  <=> ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f549,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f548,f92,f83,f158,f154])).

fof(f154,plain,
    ( spl4_8
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f158,plain,
    ( spl4_9
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f83,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f92,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f548,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f523,f94])).

fof(f94,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f523,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2 ),
    inference(resolution,[],[f144,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f144,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f85,f130])).

fof(f85,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f547,plain,
    ( spl4_3
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f545,f155])).

fof(f155,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f545,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(forward_demodulation,[],[f89,f130])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f544,plain,
    ( ~ spl4_3
    | spl4_9
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | ~ spl4_3
    | spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f542,f160])).

fof(f160,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f542,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f534,f231])).

fof(f231,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl4_13
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f534,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f488,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f488,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f88,f130])).

fof(f88,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f485,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f478,f397])).

fof(f397,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f382,f70])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f382,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f132,f377])).

fof(f377,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f113,f293])).

fof(f293,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f113,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f113,plain,
    ( sK0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f478,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f477,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f477,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f468,f411])).

fof(f411,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f394,f93])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f394,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f351,f377])).

fof(f351,plain,
    ( sK0 = k1_relset_1(sK0,sK1,k7_relat_1(sK3,sK0))
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f339,f349])).

fof(f349,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK3,sK0))
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f231,f113])).

fof(f339,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,sK0)) = k1_relat_1(k7_relat_1(sK3,sK0))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f211,f113])).

fof(f211,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_8 ),
    inference(resolution,[],[f155,f65])).

fof(f468,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0))
    | ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f422,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f422,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f279,f293])).

fof(f279,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f144,f93])).

fof(f375,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl4_7
    | spl4_8 ),
    inference(subsumption_resolution,[],[f373,f132])).

fof(f373,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7
    | spl4_8 ),
    inference(forward_demodulation,[],[f156,f113])).

fof(f156,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f371,plain,
    ( spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f365,f132])).

fof(f365,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f364,f130])).

fof(f364,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f89,f113])).

fof(f332,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_7
    | spl4_11 ),
    inference(subsumption_resolution,[],[f330,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f330,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | ~ spl4_7
    | spl4_11 ),
    inference(forward_demodulation,[],[f201,f293])).

fof(f201,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_11 ),
    inference(subsumption_resolution,[],[f200,f126])).

fof(f126,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f43,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f200,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f199,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f199,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_11 ),
    inference(superposition,[],[f197,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f197,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_11
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f315,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(subsumption_resolution,[],[f298,f53])).

fof(f298,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(backward_demodulation,[],[f236,f293])).

fof(f236,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_12 ),
    inference(subsumption_resolution,[],[f235,f126])).

fof(f235,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_12 ),
    inference(subsumption_resolution,[],[f234,f72])).

fof(f234,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_12 ),
    inference(superposition,[],[f227,f68])).

fof(f227,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_12
  <=> r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f273,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f262,f53])).

fof(f262,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f109,f98])).

fof(f109,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f239,plain,
    ( spl4_4
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f237,f44])).

fof(f44,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f237,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_4
    | spl4_12 ),
    inference(forward_demodulation,[],[f236,f134])).

fof(f134,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(forward_demodulation,[],[f125,f118])).

fof(f118,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f117,f43])).

fof(f117,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f116,f94])).

fof(f116,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f42,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f42,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f125,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f43,f65])).

fof(f233,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f221,f195,f229,f225])).

fof(f221,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2)))
    | ~ spl4_11 ),
    inference(resolution,[],[f196,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f196,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f195])).

fof(f204,plain,
    ( spl4_4
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f202,f44])).

fof(f202,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_4
    | spl4_11 ),
    inference(forward_demodulation,[],[f201,f134])).

fof(f198,plain,
    ( spl4_10
    | ~ spl4_11
    | spl4_8 ),
    inference(avatar_split_clause,[],[f189,f154,f195,f192])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_8 ),
    inference(resolution,[],[f156,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f143,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f133,f131])).

fof(f131,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl4_1 ),
    inference(backward_demodulation,[],[f81,f130])).

fof(f81,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f133,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f128,f130])).

fof(f128,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f119,f41])).

fof(f119,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f115,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f104,f111,f107])).

fof(f104,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f44,f57])).

fof(f99,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f45,f96,f92])).

fof(f45,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f46,f87,f83,f79])).

fof(f46,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (25688)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.47  % (25680)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (25671)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (25667)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (25668)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (25678)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (25670)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (25669)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (25676)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (25690)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (25682)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (25673)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (25683)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (25672)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (25674)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (25675)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (25689)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (25692)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (25679)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (25678)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f579,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f90,f99,f115,f143,f198,f204,f233,f239,f273,f315,f332,f371,f375,f485,f544,f547,f549,f578])).
% 0.20/0.53  fof(f578,plain,(
% 0.20/0.53    ~spl4_10),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f574])).
% 0.20/0.53  fof(f574,plain,(
% 0.20/0.53    $false | ~spl4_10),
% 0.20/0.53    inference(resolution,[],[f193,f132])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.53    inference(backward_demodulation,[],[f129,f130])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f121,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f15])).
% 0.20/0.53  fof(f15,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) | ~v1_funct_1(sK3)) )),
% 0.20/0.53    inference(resolution,[],[f43,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f120,f41])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.20/0.53    inference(resolution,[],[f43,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl4_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f192])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    spl4_10 <=> ! [X0] : ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.53  fof(f549,plain,(
% 0.20/0.53    ~spl4_8 | ~spl4_9 | spl4_2 | spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f548,f92,f83,f158,f154])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    spl4_8 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    spl4_9 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    spl4_4 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.53  fof(f548,plain,(
% 0.20/0.53    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | spl4_4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f523,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | spl4_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f92])).
% 0.20/0.53  fof(f523,plain,(
% 0.20/0.53    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_2),
% 0.20/0.53    inference(resolution,[],[f144,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.53    inference(forward_demodulation,[],[f85,f130])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f83])).
% 0.20/0.53  fof(f547,plain,(
% 0.20/0.53    spl4_3 | ~spl4_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f546])).
% 0.20/0.53  fof(f546,plain,(
% 0.20/0.53    $false | (spl4_3 | ~spl4_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f545,f155])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f154])).
% 0.20/0.53  fof(f545,plain,(
% 0.20/0.53    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.53    inference(forward_demodulation,[],[f89,f130])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f544,plain,(
% 0.20/0.53    ~spl4_3 | spl4_9 | ~spl4_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f543])).
% 0.20/0.53  fof(f543,plain,(
% 0.20/0.53    $false | (~spl4_3 | spl4_9 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f542,f160])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f158])).
% 0.20/0.53  fof(f542,plain,(
% 0.20/0.53    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl4_3 | ~spl4_13)),
% 0.20/0.53    inference(forward_demodulation,[],[f534,f231])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f229])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    spl4_13 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.53  fof(f534,plain,(
% 0.20/0.53    k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_3),
% 0.20/0.53    inference(resolution,[],[f488,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f488,plain,(
% 0.20/0.53    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.20/0.53    inference(backward_demodulation,[],[f88,f130])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f87])).
% 0.20/0.53  fof(f485,plain,(
% 0.20/0.53    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f484])).
% 0.20/0.53  fof(f484,plain,(
% 0.20/0.53    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f478,f397])).
% 0.20/0.53  fof(f397,plain,(
% 0.20/0.53    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_5 | ~spl4_7)),
% 0.20/0.53    inference(forward_demodulation,[],[f382,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(flattening,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.53  fof(f382,plain,(
% 0.20/0.53    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))) ) | (~spl4_5 | ~spl4_7)),
% 0.20/0.53    inference(backward_demodulation,[],[f132,f377])).
% 0.20/0.53  fof(f377,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | (~spl4_5 | ~spl4_7)),
% 0.20/0.53    inference(backward_demodulation,[],[f113,f293])).
% 0.20/0.53  fof(f293,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | (~spl4_5 | ~spl4_7)),
% 0.20/0.53    inference(forward_demodulation,[],[f113,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~spl4_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    spl4_5 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    sK0 = sK2 | ~spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl4_7 <=> sK0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f478,plain,(
% 0.20/0.53    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.53    inference(forward_demodulation,[],[f477,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f477,plain,(
% 0.20/0.53    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f468,f411])).
% 0.20/0.53  fof(f411,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) | (~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.53    inference(backward_demodulation,[],[f394,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | ~spl4_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f92])).
% 0.20/0.53  fof(f394,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,k1_xboole_0)) | (~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.53    inference(backward_demodulation,[],[f351,f377])).
% 0.20/0.53  fof(f351,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,k7_relat_1(sK3,sK0)) | (~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.53    inference(backward_demodulation,[],[f339,f349])).
% 0.20/0.53  fof(f349,plain,(
% 0.20/0.53    sK0 = k1_relat_1(k7_relat_1(sK3,sK0)) | (~spl4_7 | ~spl4_13)),
% 0.20/0.53    inference(forward_demodulation,[],[f231,f113])).
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,k7_relat_1(sK3,sK0)) = k1_relat_1(k7_relat_1(sK3,sK0)) | (~spl4_7 | ~spl4_8)),
% 0.20/0.53    inference(backward_demodulation,[],[f211,f113])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_8),
% 0.20/0.53    inference(resolution,[],[f155,f65])).
% 0.20/0.53  fof(f468,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) | ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.53    inference(resolution,[],[f422,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f422,plain,(
% 0.20/0.53    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.53    inference(forward_demodulation,[],[f279,f293])).
% 0.20/0.53  fof(f279,plain,(
% 0.20/0.53    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 0.20/0.53    inference(backward_demodulation,[],[f144,f93])).
% 0.20/0.53  fof(f375,plain,(
% 0.20/0.53    ~spl4_7 | spl4_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f374])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    $false | (~spl4_7 | spl4_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f373,f132])).
% 0.20/0.53  fof(f373,plain,(
% 0.20/0.53    ~m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_7 | spl4_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f156,f113])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f154])).
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    spl4_3 | ~spl4_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f370])).
% 0.20/0.53  fof(f370,plain,(
% 0.20/0.53    $false | (spl4_3 | ~spl4_7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f365,f132])).
% 0.20/0.53  fof(f365,plain,(
% 0.20/0.53    ~m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 0.20/0.53    inference(forward_demodulation,[],[f364,f130])).
% 0.20/0.53  fof(f364,plain,(
% 0.20/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 0.20/0.53    inference(forward_demodulation,[],[f89,f113])).
% 0.20/0.53  fof(f332,plain,(
% 0.20/0.53    ~spl4_5 | ~spl4_7 | spl4_11),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f331])).
% 0.20/0.53  fof(f331,plain,(
% 0.20/0.53    $false | (~spl4_5 | ~spl4_7 | spl4_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f330,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f330,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | ~spl4_7 | spl4_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f201,f293])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_11),
% 0.20/0.53    inference(subsumption_resolution,[],[f200,f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    v1_relat_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f43,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_11),
% 0.20/0.53    inference(subsumption_resolution,[],[f199,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_11),
% 0.20/0.53    inference(superposition,[],[f197,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f195])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    spl4_11 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.53  fof(f315,plain,(
% 0.20/0.53    ~spl4_5 | ~spl4_7 | spl4_12),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f314])).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    $false | (~spl4_5 | ~spl4_7 | spl4_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f298,f53])).
% 0.20/0.53  fof(f298,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | ~spl4_7 | spl4_12)),
% 0.20/0.53    inference(backward_demodulation,[],[f236,f293])).
% 0.20/0.53  fof(f236,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_12),
% 0.20/0.53    inference(subsumption_resolution,[],[f235,f126])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_12),
% 0.20/0.53    inference(subsumption_resolution,[],[f234,f72])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_12),
% 0.20/0.53    inference(superposition,[],[f227,f68])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2))) | spl4_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f225])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    spl4_12 <=> r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.53  fof(f273,plain,(
% 0.20/0.53    ~spl4_5 | spl4_6),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f272])).
% 0.20/0.53  fof(f272,plain,(
% 0.20/0.53    $false | (~spl4_5 | spl4_6)),
% 0.20/0.53    inference(subsumption_resolution,[],[f262,f53])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_6)),
% 0.20/0.53    inference(backward_demodulation,[],[f109,f98])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ~r1_tarski(sK0,sK2) | spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl4_6 <=> r1_tarski(sK0,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f239,plain,(
% 0.20/0.53    spl4_4 | spl4_12),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    $false | (spl4_4 | spl4_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f237,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    r1_tarski(sK2,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f237,plain,(
% 0.20/0.53    ~r1_tarski(sK2,sK0) | (spl4_4 | spl4_12)),
% 0.20/0.53    inference(forward_demodulation,[],[f236,f134])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | spl4_4),
% 0.20/0.53    inference(forward_demodulation,[],[f125,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f117,f43])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f116,f94])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(resolution,[],[f42,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f43,f65])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    ~spl4_12 | spl4_13 | ~spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f221,f195,f229,f225])).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2))) | ~spl4_11),
% 0.20/0.53    inference(resolution,[],[f196,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~spl4_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f195])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    spl4_4 | spl4_11),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    $false | (spl4_4 | spl4_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f202,f44])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    ~r1_tarski(sK2,sK0) | (spl4_4 | spl4_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f201,f134])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    spl4_10 | ~spl4_11 | spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f189,f154,f195,f192])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_8),
% 0.20/0.53    inference(resolution,[],[f156,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    spl4_1),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f139])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    $false | spl4_1),
% 0.20/0.53    inference(resolution,[],[f133,f131])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl4_1),
% 0.20/0.53    inference(backward_demodulation,[],[f81,f130])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 0.20/0.53    inference(backward_demodulation,[],[f128,f130])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f119,f41])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 0.20/0.53    inference(resolution,[],[f43,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ~spl4_6 | spl4_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f104,f111,f107])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 0.20/0.53    inference(resolution,[],[f44,f57])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ~spl4_4 | spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f45,f96,f92])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f46,f87,f83,f79])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (25678)------------------------------
% 0.20/0.53  % (25678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25678)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (25678)Memory used [KB]: 10874
% 0.20/0.53  % (25678)Time elapsed: 0.120 s
% 0.20/0.53  % (25678)------------------------------
% 0.20/0.53  % (25678)------------------------------
% 0.20/0.53  % (25681)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (25691)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (25686)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (25685)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.55  % (25684)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.55  % (25666)Success in time 0.192 s
%------------------------------------------------------------------------------
