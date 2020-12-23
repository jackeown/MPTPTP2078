%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:21 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 719 expanded)
%              Number of leaves         :   29 ( 195 expanded)
%              Depth                    :   19
%              Number of atoms          :  557 (3686 expanded)
%              Number of equality atoms :  104 ( 582 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f875,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f117,f127,f131,f140,f190,f213,f251,f260,f415,f474,f531,f568,f655,f856])).

fof(f856,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f844])).

fof(f844,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(resolution,[],[f702,f657])).

fof(f657,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f656,f410])).

fof(f410,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl3_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f656,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f105,f189])).

fof(f189,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f105,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f702,plain,
    ( ! [X0] : m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f701,f410])).

fof(f701,plain,
    ( ! [X0] : m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f700,f189])).

fof(f700,plain,
    ( ! [X0] : m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f699,f278])).

fof(f278,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f277,f139])).

fof(f139,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f277,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f145,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f145,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f79,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f699,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f697,f410])).

fof(f697,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl3_5 ),
    inference(resolution,[],[f254,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f253,f224])).

fof(f224,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f223,f160])).

fof(f160,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f158,f55])).

fof(f55,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f44])).

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
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f158,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f77,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f223,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f222,f128])).

fof(f128,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f123,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f123,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f53])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f222,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f152,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f54])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),X1) )
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f252,f116])).

fof(f116,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),X1)
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f76,f221])).

fof(f221,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f220,f128])).

fof(f220,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f153,f51])).

fof(f153,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f54])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f655,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f653,f647])).

fof(f647,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f627,f189])).

fof(f627,plain,
    ( sK1 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_18 ),
    inference(superposition,[],[f224,f410])).

fof(f653,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(superposition,[],[f588,f592])).

fof(f592,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f581,f410])).

fof(f581,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f576,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f576,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f104,f189])).

fof(f104,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f588,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f587,f410])).

fof(f587,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f578,f575])).

fof(f575,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f101,f189])).

fof(f101,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f578,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f576,f92])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f568,plain,
    ( spl3_16
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | spl3_16
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f566,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f566,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | spl3_16
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f246,f414])).

fof(f414,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl3_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f246,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl3_16
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f531,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f530])).

fof(f530,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f529,f105])).

fof(f529,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f528,f250])).

fof(f250,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl3_17
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f528,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f508,f221])).

fof(f508,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_5 ),
    inference(superposition,[],[f219,f224])).

fof(f219,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f154,f116])).

fof(f154,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f132,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f132,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f118,f128])).

fof(f118,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f474,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f472,f101])).

fof(f472,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f471,f250])).

fof(f471,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f469,f221])).

fof(f469,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_5 ),
    inference(superposition,[],[f218,f224])).

fof(f218,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f155,f116])).

fof(f155,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f132,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f415,plain,
    ( spl3_18
    | spl3_19
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f406,f187,f412,f408])).

fof(f406,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f397,f351])).

fof(f351,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_11 ),
    inference(superposition,[],[f52,f189])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f397,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_11 ),
    inference(resolution,[],[f352,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f352,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_11 ),
    inference(superposition,[],[f53,f189])).

fof(f260,plain,
    ( ~ spl3_10
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl3_10
    | spl3_17 ),
    inference(subsumption_resolution,[],[f256,f249])).

fof(f249,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f248])).

fof(f256,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f185,f161])).

fof(f161,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f78,f53])).

fof(f185,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f251,plain,
    ( ~ spl3_16
    | spl3_17 ),
    inference(avatar_split_clause,[],[f241,f248,f244])).

fof(f241,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f215,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f215,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f175,f128])).

fof(f175,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f144,f69])).

fof(f144,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f79,f53])).

fof(f213,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl3_6 ),
    inference(resolution,[],[f135,f68])).

fof(f135,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_6
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f190,plain,
    ( spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f181,f187,f183])).

fof(f181,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f179,f52])).

fof(f179,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f80,f53])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f140,plain,
    ( spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f124,f137,f134])).

fof(f124,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f59,f58])).

fof(f131,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f129,f128])).

fof(f129,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f118,f97])).

fof(f97,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f127,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f125,f68])).

fof(f125,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_4 ),
    inference(subsumption_resolution,[],[f123,f112])).

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f117,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f108,f114,f110])).

fof(f108,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f51])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f106,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f56,f103,f99,f95])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (2939)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (2947)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  % (2933)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (2931)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (2929)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (2926)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (2930)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (2950)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (2951)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (2938)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (2936)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (2942)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (2943)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (2949)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (2927)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (2941)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (2946)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (2948)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (2935)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (2934)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (2937)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (2945)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (2928)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (2944)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (2932)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (2940)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.34/0.54  % (2936)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f875,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(avatar_sat_refutation,[],[f106,f117,f127,f131,f140,f190,f213,f251,f260,f415,f474,f531,f568,f655,f856])).
% 1.34/0.54  fof(f856,plain,(
% 1.34/0.54    spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_11 | ~spl3_18),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f844])).
% 1.34/0.54  fof(f844,plain,(
% 1.34/0.54    $false | (spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(resolution,[],[f702,f657])).
% 1.34/0.54  fof(f657,plain,(
% 1.34/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(forward_demodulation,[],[f656,f410])).
% 1.34/0.54  fof(f410,plain,(
% 1.34/0.54    k1_xboole_0 = sK2 | ~spl3_18),
% 1.34/0.54    inference(avatar_component_clause,[],[f408])).
% 1.34/0.54  fof(f408,plain,(
% 1.34/0.54    spl3_18 <=> k1_xboole_0 = sK2),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.34/0.54  fof(f656,plain,(
% 1.34/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_11)),
% 1.34/0.54    inference(forward_demodulation,[],[f105,f189])).
% 1.34/0.54  fof(f189,plain,(
% 1.34/0.54    k1_xboole_0 = sK1 | ~spl3_11),
% 1.34/0.54    inference(avatar_component_clause,[],[f187])).
% 1.34/0.54  fof(f187,plain,(
% 1.34/0.54    spl3_11 <=> k1_xboole_0 = sK1),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.34/0.54  fof(f105,plain,(
% 1.34/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 1.34/0.54    inference(avatar_component_clause,[],[f103])).
% 1.34/0.54  fof(f103,plain,(
% 1.34/0.54    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.34/0.54  fof(f702,plain,(
% 1.34/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(forward_demodulation,[],[f701,f410])).
% 1.34/0.54  fof(f701,plain,(
% 1.34/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(forward_demodulation,[],[f700,f189])).
% 1.34/0.54  fof(f700,plain,(
% 1.34/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_18)),
% 1.34/0.54    inference(subsumption_resolution,[],[f699,f278])).
% 1.34/0.54  fof(f278,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | ~spl3_7),
% 1.34/0.54    inference(subsumption_resolution,[],[f277,f139])).
% 1.34/0.54  fof(f139,plain,(
% 1.34/0.54    v1_relat_1(k1_xboole_0) | ~spl3_7),
% 1.34/0.54    inference(avatar_component_clause,[],[f137])).
% 1.34/0.54  fof(f137,plain,(
% 1.34/0.54    spl3_7 <=> v1_relat_1(k1_xboole_0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.34/0.54  fof(f277,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.34/0.54    inference(resolution,[],[f145,f69])).
% 1.34/0.54  fof(f69,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f46])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.34/0.54  fof(f145,plain,(
% 1.34/0.54    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.34/0.54    inference(resolution,[],[f79,f58])).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.34/0.54  fof(f79,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f39])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f21])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.34/0.54    inference(pure_predicate_removal,[],[f13])).
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.54  fof(f699,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl3_5 | ~spl3_18)),
% 1.34/0.54    inference(forward_demodulation,[],[f697,f410])).
% 1.34/0.54  fof(f697,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl3_5),
% 1.34/0.54    inference(resolution,[],[f254,f87])).
% 1.34/0.54  fof(f87,plain,(
% 1.34/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.54    inference(equality_resolution,[],[f72])).
% 1.34/0.54  fof(f72,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f48])).
% 1.34/0.54  fof(f48,plain,(
% 1.34/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.54    inference(flattening,[],[f47])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.54  fof(f254,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(sK1,X1) | ~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_5),
% 1.34/0.54    inference(forward_demodulation,[],[f253,f224])).
% 1.34/0.54  fof(f224,plain,(
% 1.34/0.54    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.34/0.54    inference(forward_demodulation,[],[f223,f160])).
% 1.34/0.54  fof(f160,plain,(
% 1.34/0.54    sK1 = k2_relat_1(sK2)),
% 1.34/0.54    inference(forward_demodulation,[],[f158,f55])).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f45])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f44])).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.34/0.54    inference(flattening,[],[f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.34/0.54    inference(ennf_transformation,[],[f20])).
% 1.34/0.54  fof(f20,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.34/0.54    inference(negated_conjecture,[],[f19])).
% 1.34/0.54  fof(f19,conjecture,(
% 1.34/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.34/0.54  fof(f158,plain,(
% 1.34/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.34/0.54    inference(resolution,[],[f77,f53])).
% 1.34/0.54  fof(f53,plain,(
% 1.34/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.34/0.54    inference(cnf_transformation,[],[f45])).
% 1.34/0.54  fof(f77,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f37])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f15])).
% 1.34/0.54  fof(f15,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.34/0.54  fof(f223,plain,(
% 1.34/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.34/0.54    inference(subsumption_resolution,[],[f222,f128])).
% 1.34/0.54  fof(f128,plain,(
% 1.34/0.54    v1_relat_1(sK2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f123,f68])).
% 1.34/0.54  fof(f68,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.54  fof(f123,plain,(
% 1.34/0.54    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.34/0.54    inference(resolution,[],[f59,f53])).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.54  fof(f222,plain,(
% 1.34/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f152,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    v1_funct_1(sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f45])).
% 1.34/0.54  fof(f152,plain,(
% 1.34/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.34/0.54    inference(resolution,[],[f65,f54])).
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    v2_funct_1(sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f45])).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(flattening,[],[f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,axiom,(
% 1.34/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.34/0.54  fof(f253,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(k2_funct_1(sK2)),X1)) ) | ~spl3_5),
% 1.34/0.54    inference(subsumption_resolution,[],[f252,f116])).
% 1.34/0.54  fof(f116,plain,(
% 1.34/0.54    v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.34/0.54    inference(avatar_component_clause,[],[f114])).
% 1.34/0.54  fof(f114,plain,(
% 1.34/0.54    spl3_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.34/0.54  fof(f252,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(k2_funct_1(sK2)),X1) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 1.34/0.54    inference(superposition,[],[f76,f221])).
% 1.34/0.54  fof(f221,plain,(
% 1.34/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.34/0.54    inference(subsumption_resolution,[],[f220,f128])).
% 1.34/0.54  fof(f220,plain,(
% 1.34/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f153,f51])).
% 1.34/0.54  fof(f153,plain,(
% 1.34/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.34/0.54    inference(resolution,[],[f66,f54])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f76,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.34/0.54    inference(flattening,[],[f35])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.34/0.54    inference(ennf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.34/0.54  fof(f655,plain,(
% 1.34/0.54    spl3_2 | ~spl3_3 | ~spl3_11 | ~spl3_18),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f654])).
% 1.34/0.54  fof(f654,plain,(
% 1.34/0.54    $false | (spl3_2 | ~spl3_3 | ~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(subsumption_resolution,[],[f653,f647])).
% 1.34/0.54  fof(f647,plain,(
% 1.34/0.54    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(forward_demodulation,[],[f627,f189])).
% 1.34/0.54  fof(f627,plain,(
% 1.34/0.54    sK1 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_18),
% 1.34/0.54    inference(superposition,[],[f224,f410])).
% 1.34/0.54  fof(f653,plain,(
% 1.34/0.54    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | (spl3_2 | ~spl3_3 | ~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(superposition,[],[f588,f592])).
% 1.34/0.54  fof(f592,plain,(
% 1.34/0.54    k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (~spl3_3 | ~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(forward_demodulation,[],[f581,f410])).
% 1.34/0.54  fof(f581,plain,(
% 1.34/0.54    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (~spl3_3 | ~spl3_11)),
% 1.34/0.54    inference(resolution,[],[f576,f78])).
% 1.34/0.54  fof(f78,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f38])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.34/0.54  fof(f576,plain,(
% 1.34/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_3 | ~spl3_11)),
% 1.34/0.54    inference(forward_demodulation,[],[f104,f189])).
% 1.34/0.54  fof(f104,plain,(
% 1.34/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_3),
% 1.34/0.54    inference(avatar_component_clause,[],[f103])).
% 1.34/0.54  fof(f588,plain,(
% 1.34/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (spl3_2 | ~spl3_3 | ~spl3_11 | ~spl3_18)),
% 1.34/0.54    inference(forward_demodulation,[],[f587,f410])).
% 1.34/0.54  fof(f587,plain,(
% 1.34/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl3_2 | ~spl3_3 | ~spl3_11)),
% 1.34/0.54    inference(subsumption_resolution,[],[f578,f575])).
% 1.34/0.54  fof(f575,plain,(
% 1.34/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_11)),
% 1.34/0.54    inference(forward_demodulation,[],[f101,f189])).
% 1.34/0.54  fof(f101,plain,(
% 1.34/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 1.34/0.54    inference(avatar_component_clause,[],[f99])).
% 1.34/0.54  fof(f99,plain,(
% 1.34/0.54    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.34/0.54  fof(f578,plain,(
% 1.34/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (~spl3_3 | ~spl3_11)),
% 1.34/0.54    inference(resolution,[],[f576,f92])).
% 1.34/0.54  fof(f92,plain,(
% 1.34/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.34/0.54    inference(equality_resolution,[],[f83])).
% 1.34/0.54  fof(f83,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f50])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(nnf_transformation,[],[f41])).
% 1.34/0.54  fof(f41,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(flattening,[],[f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.34/0.54  fof(f568,plain,(
% 1.34/0.54    spl3_16 | ~spl3_19),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f567])).
% 1.34/0.54  fof(f567,plain,(
% 1.34/0.54    $false | (spl3_16 | ~spl3_19)),
% 1.34/0.54    inference(subsumption_resolution,[],[f566,f57])).
% 1.34/0.54  fof(f57,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.34/0.54  fof(f566,plain,(
% 1.34/0.54    ~r1_tarski(k1_xboole_0,k1_relat_1(sK2)) | (spl3_16 | ~spl3_19)),
% 1.34/0.54    inference(forward_demodulation,[],[f246,f414])).
% 1.34/0.54  fof(f414,plain,(
% 1.34/0.54    k1_xboole_0 = sK0 | ~spl3_19),
% 1.34/0.54    inference(avatar_component_clause,[],[f412])).
% 1.34/0.54  fof(f412,plain,(
% 1.34/0.54    spl3_19 <=> k1_xboole_0 = sK0),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.34/0.54  fof(f246,plain,(
% 1.34/0.54    ~r1_tarski(sK0,k1_relat_1(sK2)) | spl3_16),
% 1.34/0.54    inference(avatar_component_clause,[],[f244])).
% 1.34/0.54  fof(f244,plain,(
% 1.34/0.54    spl3_16 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.34/0.54  fof(f531,plain,(
% 1.34/0.54    spl3_3 | ~spl3_5 | ~spl3_17),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f530])).
% 1.34/0.54  fof(f530,plain,(
% 1.34/0.54    $false | (spl3_3 | ~spl3_5 | ~spl3_17)),
% 1.34/0.54    inference(subsumption_resolution,[],[f529,f105])).
% 1.34/0.54  fof(f529,plain,(
% 1.34/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_5 | ~spl3_17)),
% 1.34/0.54    inference(forward_demodulation,[],[f528,f250])).
% 1.34/0.54  fof(f250,plain,(
% 1.34/0.54    sK0 = k1_relat_1(sK2) | ~spl3_17),
% 1.34/0.54    inference(avatar_component_clause,[],[f248])).
% 1.34/0.54  fof(f248,plain,(
% 1.34/0.54    spl3_17 <=> sK0 = k1_relat_1(sK2)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.34/0.54  fof(f528,plain,(
% 1.34/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl3_5),
% 1.34/0.54    inference(forward_demodulation,[],[f508,f221])).
% 1.34/0.54  fof(f508,plain,(
% 1.34/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~spl3_5),
% 1.34/0.54    inference(superposition,[],[f219,f224])).
% 1.34/0.54  fof(f219,plain,(
% 1.34/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_5),
% 1.34/0.54    inference(subsumption_resolution,[],[f154,f116])).
% 1.34/0.54  fof(f154,plain,(
% 1.34/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.34/0.54    inference(resolution,[],[f132,f62])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(flattening,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f18])).
% 1.34/0.54  fof(f18,axiom,(
% 1.34/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.34/0.54  fof(f132,plain,(
% 1.34/0.54    v1_funct_1(k2_funct_1(sK2))),
% 1.34/0.54    inference(subsumption_resolution,[],[f118,f128])).
% 1.34/0.54  fof(f118,plain,(
% 1.34/0.54    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.34/0.54    inference(resolution,[],[f64,f51])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(flattening,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.34/0.54  fof(f474,plain,(
% 1.34/0.54    spl3_2 | ~spl3_5 | ~spl3_17),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f473])).
% 1.34/0.54  fof(f473,plain,(
% 1.34/0.54    $false | (spl3_2 | ~spl3_5 | ~spl3_17)),
% 1.34/0.54    inference(subsumption_resolution,[],[f472,f101])).
% 1.34/0.54  fof(f472,plain,(
% 1.34/0.54    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_5 | ~spl3_17)),
% 1.34/0.54    inference(forward_demodulation,[],[f471,f250])).
% 1.34/0.54  fof(f471,plain,(
% 1.34/0.54    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~spl3_5),
% 1.34/0.54    inference(forward_demodulation,[],[f469,f221])).
% 1.34/0.54  fof(f469,plain,(
% 1.34/0.54    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~spl3_5),
% 1.34/0.54    inference(superposition,[],[f218,f224])).
% 1.34/0.54  fof(f218,plain,(
% 1.34/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_5),
% 1.34/0.54    inference(subsumption_resolution,[],[f155,f116])).
% 1.34/0.54  fof(f155,plain,(
% 1.34/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.34/0.54    inference(resolution,[],[f132,f61])).
% 1.34/0.54  fof(f61,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f27])).
% 1.34/0.54  fof(f415,plain,(
% 1.34/0.54    spl3_18 | spl3_19 | ~spl3_11),
% 1.34/0.54    inference(avatar_split_clause,[],[f406,f187,f412,f408])).
% 1.34/0.54  fof(f406,plain,(
% 1.34/0.54    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_11),
% 1.34/0.54    inference(subsumption_resolution,[],[f397,f351])).
% 1.34/0.54  fof(f351,plain,(
% 1.34/0.54    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl3_11),
% 1.34/0.54    inference(superposition,[],[f52,f189])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    v1_funct_2(sK2,sK0,sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f45])).
% 1.34/0.54  fof(f397,plain,(
% 1.34/0.54    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_11),
% 1.34/0.54    inference(resolution,[],[f352,f91])).
% 1.34/0.54  fof(f91,plain,(
% 1.34/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.34/0.54    inference(equality_resolution,[],[f84])).
% 1.34/0.54  fof(f84,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f50])).
% 1.34/0.54  fof(f352,plain,(
% 1.34/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_11),
% 1.34/0.54    inference(superposition,[],[f53,f189])).
% 1.34/0.54  fof(f260,plain,(
% 1.34/0.54    ~spl3_10 | spl3_17),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f259])).
% 1.34/0.54  fof(f259,plain,(
% 1.34/0.54    $false | (~spl3_10 | spl3_17)),
% 1.34/0.54    inference(subsumption_resolution,[],[f256,f249])).
% 1.34/0.54  fof(f249,plain,(
% 1.34/0.54    sK0 != k1_relat_1(sK2) | spl3_17),
% 1.34/0.54    inference(avatar_component_clause,[],[f248])).
% 1.34/0.54  fof(f256,plain,(
% 1.34/0.54    sK0 = k1_relat_1(sK2) | ~spl3_10),
% 1.34/0.54    inference(superposition,[],[f185,f161])).
% 1.34/0.54  fof(f161,plain,(
% 1.34/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.34/0.54    inference(resolution,[],[f78,f53])).
% 1.34/0.54  fof(f185,plain,(
% 1.34/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_10),
% 1.34/0.54    inference(avatar_component_clause,[],[f183])).
% 1.34/0.54  fof(f183,plain,(
% 1.34/0.54    spl3_10 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.34/0.54  fof(f251,plain,(
% 1.34/0.54    ~spl3_16 | spl3_17),
% 1.34/0.54    inference(avatar_split_clause,[],[f241,f248,f244])).
% 1.34/0.54  fof(f241,plain,(
% 1.34/0.54    sK0 = k1_relat_1(sK2) | ~r1_tarski(sK0,k1_relat_1(sK2))),
% 1.34/0.54    inference(resolution,[],[f215,f73])).
% 1.34/0.54  fof(f73,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f48])).
% 1.34/0.54  fof(f215,plain,(
% 1.34/0.54    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f175,f128])).
% 1.34/0.54  fof(f175,plain,(
% 1.34/0.54    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.34/0.54    inference(resolution,[],[f144,f69])).
% 1.34/0.54  fof(f144,plain,(
% 1.34/0.54    v4_relat_1(sK2,sK0)),
% 1.34/0.54    inference(resolution,[],[f79,f53])).
% 1.34/0.54  fof(f213,plain,(
% 1.34/0.54    ~spl3_6),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f208])).
% 1.34/0.54  fof(f208,plain,(
% 1.34/0.54    $false | ~spl3_6),
% 1.34/0.54    inference(resolution,[],[f135,f68])).
% 1.34/0.54  fof(f135,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl3_6),
% 1.34/0.54    inference(avatar_component_clause,[],[f134])).
% 1.34/0.54  fof(f134,plain,(
% 1.34/0.54    spl3_6 <=> ! [X0] : ~v1_relat_1(X0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.34/0.54  fof(f190,plain,(
% 1.34/0.54    spl3_10 | spl3_11),
% 1.34/0.54    inference(avatar_split_clause,[],[f181,f187,f183])).
% 1.34/0.54  fof(f181,plain,(
% 1.34/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f179,f52])).
% 1.34/0.54  fof(f179,plain,(
% 1.34/0.54    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.34/0.54    inference(resolution,[],[f80,f53])).
% 1.34/0.54  fof(f80,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f50])).
% 1.34/0.54  fof(f140,plain,(
% 1.34/0.54    spl3_6 | spl3_7),
% 1.34/0.54    inference(avatar_split_clause,[],[f124,f137,f134])).
% 1.34/0.54  fof(f124,plain,(
% 1.34/0.54    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(resolution,[],[f59,f58])).
% 1.34/0.54  fof(f131,plain,(
% 1.34/0.54    spl3_1),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f130])).
% 1.34/0.54  fof(f130,plain,(
% 1.34/0.54    $false | spl3_1),
% 1.34/0.54    inference(subsumption_resolution,[],[f129,f128])).
% 1.34/0.54  fof(f129,plain,(
% 1.34/0.54    ~v1_relat_1(sK2) | spl3_1),
% 1.34/0.54    inference(subsumption_resolution,[],[f118,f97])).
% 1.34/0.54  fof(f97,plain,(
% 1.34/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 1.34/0.54    inference(avatar_component_clause,[],[f95])).
% 1.34/0.54  fof(f95,plain,(
% 1.34/0.54    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.34/0.54  fof(f127,plain,(
% 1.34/0.54    spl3_4),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f126])).
% 1.34/0.54  fof(f126,plain,(
% 1.34/0.54    $false | spl3_4),
% 1.34/0.54    inference(subsumption_resolution,[],[f125,f68])).
% 1.34/0.54  fof(f125,plain,(
% 1.34/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_4),
% 1.34/0.54    inference(subsumption_resolution,[],[f123,f112])).
% 1.34/0.54  fof(f112,plain,(
% 1.34/0.54    ~v1_relat_1(sK2) | spl3_4),
% 1.34/0.54    inference(avatar_component_clause,[],[f110])).
% 1.34/0.54  fof(f110,plain,(
% 1.34/0.54    spl3_4 <=> v1_relat_1(sK2)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.34/0.54  fof(f117,plain,(
% 1.34/0.54    ~spl3_4 | spl3_5),
% 1.34/0.54    inference(avatar_split_clause,[],[f108,f114,f110])).
% 1.34/0.54  fof(f108,plain,(
% 1.34/0.54    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.34/0.54    inference(resolution,[],[f63,f51])).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  fof(f106,plain,(
% 1.34/0.54    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.34/0.54    inference(avatar_split_clause,[],[f56,f103,f99,f95])).
% 1.34/0.54  fof(f56,plain,(
% 1.34/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.34/0.54    inference(cnf_transformation,[],[f45])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (2936)------------------------------
% 1.34/0.54  % (2936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (2936)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (2936)Memory used [KB]: 11001
% 1.34/0.54  % (2936)Time elapsed: 0.118 s
% 1.34/0.54  % (2936)------------------------------
% 1.34/0.54  % (2936)------------------------------
% 1.34/0.54  % (2925)Success in time 0.183 s
%------------------------------------------------------------------------------
