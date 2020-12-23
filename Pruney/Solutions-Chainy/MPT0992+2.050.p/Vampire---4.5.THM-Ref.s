%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 495 expanded)
%              Number of leaves         :   41 ( 169 expanded)
%              Depth                    :   13
%              Number of atoms          :  589 (2332 expanded)
%              Number of equality atoms :  121 ( 620 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1395,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f109,f160,f208,f213,f302,f363,f393,f548,f549,f550,f587,f606,f631,f789,f809,f844,f849,f951,f1025,f1049,f1086,f1104,f1111,f1140,f1141,f1391])).

fof(f1391,plain,
    ( ~ spl4_5
    | spl4_75
    | ~ spl4_80 ),
    inference(avatar_contradiction_clause,[],[f1377])).

fof(f1377,plain,
    ( $false
    | ~ spl4_5
    | spl4_75
    | ~ spl4_80 ),
    inference(unit_resulting_resolution,[],[f247,f1341,f1166])).

fof(f1166,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | r1_tarski(X0,X0) )
    | ~ spl4_5 ),
    inference(superposition,[],[f247,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f1341,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_75
    | ~ spl4_80 ),
    inference(backward_demodulation,[],[f1109,f1137])).

fof(f1137,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f1135,plain,
    ( spl4_80
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1109,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | spl4_75 ),
    inference(avatar_component_clause,[],[f1107])).

fof(f1107,plain,
    ( spl4_75
  <=> r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f247,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f222,f223])).

fof(f223,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f222,f63])).

fof(f222,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f54,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f54,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f46])).

fof(f46,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f1141,plain,
    ( ~ spl4_33
    | ~ spl4_75
    | ~ spl4_49
    | spl4_30 ),
    inference(avatar_split_clause,[],[f700,f390,f717,f1107,f561])).

fof(f561,plain,
    ( spl4_33
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f717,plain,
    ( spl4_49
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f390,plain,
    ( spl4_30
  <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f700,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl4_30 ),
    inference(superposition,[],[f392,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f392,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f390])).

fof(f1140,plain,
    ( spl4_80
    | ~ spl4_24
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f1139,f295,f299,f1135])).

fof(f299,plain,
    ( spl4_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f295,plain,
    ( spl4_23
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f1139,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f681,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f681,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_23 ),
    inference(superposition,[],[f297,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f297,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f295])).

fof(f1111,plain,
    ( spl4_49
    | ~ spl4_24
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f691,f295,f299,f717])).

fof(f691,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f685,f81])).

fof(f685,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_23 ),
    inference(trivial_inequality_removal,[],[f682])).

fof(f682,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_23 ),
    inference(superposition,[],[f86,f297])).

fof(f86,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f1104,plain,(
    spl4_57 ),
    inference(avatar_contradiction_clause,[],[f1100])).

fof(f1100,plain,
    ( $false
    | spl4_57 ),
    inference(unit_resulting_resolution,[],[f54,f820])).

fof(f820,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_57 ),
    inference(avatar_component_clause,[],[f818])).

fof(f818,plain,
    ( spl4_57
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1086,plain,
    ( ~ spl4_33
    | ~ spl4_57
    | ~ spl4_40
    | spl4_72 ),
    inference(avatar_split_clause,[],[f1085,f1022,f627,f818,f561])).

fof(f627,plain,
    ( spl4_40
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1022,plain,
    ( spl4_72
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f1085,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_40
    | spl4_72 ),
    inference(forward_demodulation,[],[f1082,f629])).

fof(f629,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f627])).

fof(f1082,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_72 ),
    inference(trivial_inequality_removal,[],[f1081])).

fof(f1081,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_72 ),
    inference(superposition,[],[f1024,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1024,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1049,plain,
    ( ~ spl4_11
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f1036])).

fof(f1036,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f176,f1026,f129])).

fof(f129,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(resolution,[],[f53,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f1026,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f194,f149])).

fof(f149,plain,
    ( ! [X2] : k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_11
  <=> ! [X2] : k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f194,plain,
    ( ! [X0] : ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_16
  <=> ! [X0] : ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f176,plain,(
    ! [X5] : r1_tarski(k7_relat_1(sK3,X5),sK3) ),
    inference(resolution,[],[f130,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f130,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1025,plain,
    ( ~ spl4_18
    | ~ spl4_72
    | ~ spl4_11
    | spl4_14 ),
    inference(avatar_split_clause,[],[f1017,f180,f148,f1022,f201])).

fof(f201,plain,
    ( spl4_18
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f180,plain,
    ( spl4_14
  <=> sK2 = k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1017,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_11
    | spl4_14 ),
    inference(superposition,[],[f1015,f75])).

fof(f1015,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_11
    | spl4_14 ),
    inference(forward_demodulation,[],[f182,f149])).

fof(f182,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f951,plain,
    ( ~ spl4_10
    | ~ spl4_11
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f940])).

fof(f940,plain,
    ( $false
    | ~ spl4_10
    | ~ spl4_11
    | spl4_18 ),
    inference(unit_resulting_resolution,[],[f171,f203,f935,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f935,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f145,f149])).

fof(f145,plain,
    ( ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_10
  <=> ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f203,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f171,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) ),
    inference(resolution,[],[f130,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f849,plain,
    ( spl4_16
    | ~ spl4_17
    | spl4_3 ),
    inference(avatar_split_clause,[],[f846,f97,f196,f193])).

fof(f196,plain,
    ( spl4_17
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f97,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f846,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
        | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_3 ),
    inference(resolution,[],[f99,f76])).

fof(f99,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f844,plain,
    ( spl4_4
    | ~ spl4_14
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f828,f97,f93,f180,f102])).

fof(f102,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f93,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f828,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ spl4_3 ),
    inference(resolution,[],[f98,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f809,plain,(
    spl4_54 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | spl4_54 ),
    inference(unit_resulting_resolution,[],[f130,f788,f80])).

fof(f788,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_54 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl4_54
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f789,plain,
    ( ~ spl4_8
    | ~ spl4_6
    | ~ spl4_54
    | spl4_17 ),
    inference(avatar_split_clause,[],[f784,f196,f786,f118,f136])).

fof(f136,plain,
    ( spl4_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f118,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f784,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_17 ),
    inference(superposition,[],[f198,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f198,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f196])).

fof(f631,plain,
    ( ~ spl4_6
    | spl4_40
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f623,f122,f627,f118])).

fof(f122,plain,
    ( spl4_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f623,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(superposition,[],[f75,f124])).

fof(f124,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f606,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f53,f120])).

fof(f120,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f587,plain,(
    spl4_33 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | spl4_33 ),
    inference(unit_resulting_resolution,[],[f53,f563,f66])).

fof(f563,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f561])).

fof(f550,plain,
    ( spl4_4
    | ~ spl4_12
    | spl4_7 ),
    inference(avatar_split_clause,[],[f543,f122,f152,f102])).

fof(f152,plain,
    ( spl4_12
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f543,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f549,plain,
    ( ~ spl4_8
    | spl4_11 ),
    inference(avatar_split_clause,[],[f540,f148,f136])).

fof(f540,plain,(
    ! [X2] :
      ( k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f53,f59])).

fof(f548,plain,
    ( ~ spl4_8
    | spl4_10 ),
    inference(avatar_split_clause,[],[f539,f144,f136])).

fof(f539,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f53,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f393,plain,
    ( ~ spl4_8
    | ~ spl4_30
    | ~ spl4_24
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f388,f106,f102,f93,f299,f390,f136])).

fof(f388,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f369,f81])).

fof(f369,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK3)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f349,f59])).

fof(f349,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f348,f108])).

fof(f348,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f218,f223])).

fof(f218,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f95,f103])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f95,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f363,plain,
    ( ~ spl4_4
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | ~ spl4_4
    | spl4_24 ),
    inference(unit_resulting_resolution,[],[f220,f301])).

fof(f301,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f299])).

fof(f220,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f216,f81])).

fof(f216,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f53,f103])).

fof(f302,plain,
    ( spl4_23
    | ~ spl4_24
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f293,f106,f102,f299,f295])).

fof(f293,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f282,f81])).

fof(f282,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f246,f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f246,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f215,f108])).

fof(f215,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f52,f103])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f213,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f52,f154])).

fof(f154,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f208,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f51,f138])).

fof(f138,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f160,plain,
    ( ~ spl4_8
    | ~ spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f157,f89,f118,f136])).

fof(f89,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f157,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(resolution,[],[f91,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f109,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f55,f106,f102])).

fof(f55,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f56,f97,f93,f89])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:46:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (24666)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (24658)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (24657)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (24660)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (24677)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (24676)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (24656)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (24655)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (24668)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (24659)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (24661)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (24669)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (24666)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (24675)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (24671)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (24664)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (24662)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (24663)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (24672)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (24670)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1395,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f100,f109,f160,f208,f213,f302,f363,f393,f548,f549,f550,f587,f606,f631,f789,f809,f844,f849,f951,f1025,f1049,f1086,f1104,f1111,f1140,f1141,f1391])).
% 0.21/0.53  fof(f1391,plain,(
% 0.21/0.53    ~spl4_5 | spl4_75 | ~spl4_80),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1377])).
% 0.21/0.53  fof(f1377,plain,(
% 0.21/0.53    $false | (~spl4_5 | spl4_75 | ~spl4_80)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f247,f1341,f1166])).
% 0.21/0.53  fof(f1166,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X0)) ) | ~spl4_5),
% 0.21/0.53    inference(superposition,[],[f247,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.53  fof(f1341,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl4_75 | ~spl4_80)),
% 0.21/0.53    inference(backward_demodulation,[],[f1109,f1137])).
% 0.21/0.53  fof(f1137,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_80),
% 0.21/0.53    inference(avatar_component_clause,[],[f1135])).
% 0.21/0.53  fof(f1135,plain,(
% 0.21/0.53    spl4_80 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 0.21/0.53  fof(f1109,plain,(
% 0.21/0.53    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | spl4_75),
% 0.21/0.53    inference(avatar_component_clause,[],[f1107])).
% 0.21/0.53  fof(f1107,plain,(
% 0.21/0.53    spl4_75 <=> r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl4_5),
% 0.21/0.53    inference(backward_demodulation,[],[f222,f223])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~spl4_5),
% 0.21/0.53    inference(resolution,[],[f222,f63])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 0.21/0.53    inference(backward_demodulation,[],[f54,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | ~spl4_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    r1_tarski(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f19])).
% 0.21/0.53  fof(f19,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.53  fof(f1141,plain,(
% 0.21/0.53    ~spl4_33 | ~spl4_75 | ~spl4_49 | spl4_30),
% 0.21/0.53    inference(avatar_split_clause,[],[f700,f390,f717,f1107,f561])).
% 0.21/0.53  fof(f561,plain,(
% 0.21/0.53    spl4_33 <=> v1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.53  fof(f717,plain,(
% 0.21/0.53    spl4_49 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.53  fof(f390,plain,(
% 0.21/0.53    spl4_30 <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.53  fof(f700,plain,(
% 0.21/0.53    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~v1_relat_1(sK3) | spl4_30),
% 0.21/0.53    inference(superposition,[],[f392,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.53  fof(f392,plain,(
% 0.21/0.53    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | spl4_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f390])).
% 0.21/0.53  fof(f1140,plain,(
% 0.21/0.53    spl4_80 | ~spl4_24 | ~spl4_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f1139,f295,f299,f1135])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    spl4_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    spl4_23 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.53  fof(f1139,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3) | ~spl4_23),
% 0.21/0.53    inference(forward_demodulation,[],[f681,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(flattening,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.53  fof(f681,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_23),
% 0.21/0.53    inference(superposition,[],[f297,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl4_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f295])).
% 0.21/0.53  fof(f1111,plain,(
% 0.21/0.53    spl4_49 | ~spl4_24 | ~spl4_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f691,f295,f299,f717])).
% 0.21/0.53  fof(f691,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl4_23),
% 0.21/0.53    inference(forward_demodulation,[],[f685,f81])).
% 0.21/0.53  fof(f685,plain,(
% 0.21/0.53    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_23),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f682])).
% 0.21/0.53  fof(f682,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_23),
% 0.21/0.53    inference(superposition,[],[f86,f297])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f1104,plain,(
% 0.21/0.53    spl4_57),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1100])).
% 0.21/0.53  fof(f1100,plain,(
% 0.21/0.53    $false | spl4_57),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f54,f820])).
% 0.21/0.53  fof(f820,plain,(
% 0.21/0.53    ~r1_tarski(sK2,sK0) | spl4_57),
% 0.21/0.53    inference(avatar_component_clause,[],[f818])).
% 0.21/0.53  fof(f818,plain,(
% 0.21/0.53    spl4_57 <=> r1_tarski(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.21/0.53  fof(f1086,plain,(
% 0.21/0.53    ~spl4_33 | ~spl4_57 | ~spl4_40 | spl4_72),
% 0.21/0.53    inference(avatar_split_clause,[],[f1085,f1022,f627,f818,f561])).
% 0.21/0.53  fof(f627,plain,(
% 0.21/0.53    spl4_40 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.53  fof(f1022,plain,(
% 0.21/0.53    spl4_72 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 0.21/0.53  fof(f1085,plain,(
% 0.21/0.53    ~r1_tarski(sK2,sK0) | ~v1_relat_1(sK3) | (~spl4_40 | spl4_72)),
% 0.21/0.53    inference(forward_demodulation,[],[f1082,f629])).
% 0.21/0.53  fof(f629,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK3) | ~spl4_40),
% 0.21/0.53    inference(avatar_component_clause,[],[f627])).
% 0.21/0.53  fof(f1082,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_72),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f1081])).
% 0.21/0.53  fof(f1081,plain,(
% 0.21/0.53    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_72),
% 0.21/0.53    inference(superposition,[],[f1024,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.53  fof(f1024,plain,(
% 0.21/0.53    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_72),
% 0.21/0.53    inference(avatar_component_clause,[],[f1022])).
% 0.21/0.53  fof(f1049,plain,(
% 0.21/0.53    ~spl4_11 | ~spl4_16),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1036])).
% 0.21/0.53  fof(f1036,plain,(
% 0.21/0.53    $false | (~spl4_11 | ~spl4_16)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f176,f1026,f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X3] : (~r1_tarski(X3,sK3) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.21/0.53    inference(resolution,[],[f53,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f1026,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl4_11 | ~spl4_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f194,f149])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)) ) | ~spl4_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    spl4_11 <=> ! [X2] : k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl4_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f193])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    spl4_16 <=> ! [X0] : ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ( ! [X5] : (r1_tarski(k7_relat_1(sK3,X5),sK3)) )),
% 0.21/0.53    inference(resolution,[],[f130,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    v1_relat_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f53,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f1025,plain,(
% 0.21/0.53    ~spl4_18 | ~spl4_72 | ~spl4_11 | spl4_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f1017,f180,f148,f1022,f201])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    spl4_18 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    spl4_14 <=> sK2 = k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.53  fof(f1017,plain,(
% 0.21/0.53    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_11 | spl4_14)),
% 0.21/0.53    inference(superposition,[],[f1015,f75])).
% 0.21/0.53  fof(f1015,plain,(
% 0.21/0.53    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl4_11 | spl4_14)),
% 0.21/0.53    inference(forward_demodulation,[],[f182,f149])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f180])).
% 0.21/0.53  fof(f951,plain,(
% 0.21/0.53    ~spl4_10 | ~spl4_11 | spl4_18),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f940])).
% 0.21/0.53  fof(f940,plain,(
% 0.21/0.53    $false | (~spl4_10 | ~spl4_11 | spl4_18)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f171,f203,f935,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.53  fof(f935,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_10 | ~spl4_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f145,f149])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    spl4_10 <=> ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f201])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)) )),
% 0.21/0.53    inference(resolution,[],[f130,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.53  fof(f849,plain,(
% 0.21/0.53    spl4_16 | ~spl4_17 | spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f846,f97,f196,f193])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    spl4_17 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f846,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_3),
% 0.21/0.53    inference(resolution,[],[f99,f76])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f844,plain,(
% 0.21/0.53    spl4_4 | ~spl4_14 | spl4_2 | ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f828,f97,f93,f180,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f828,plain,(
% 0.21/0.53    v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | k1_xboole_0 = sK1 | ~spl4_3),
% 0.21/0.53    inference(resolution,[],[f98,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f809,plain,(
% 0.21/0.53    spl4_54),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f800])).
% 0.21/0.53  fof(f800,plain,(
% 0.21/0.53    $false | spl4_54),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f130,f788,f80])).
% 0.21/0.53  fof(f788,plain,(
% 0.21/0.53    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_54),
% 0.21/0.53    inference(avatar_component_clause,[],[f786])).
% 0.21/0.53  fof(f786,plain,(
% 0.21/0.53    spl4_54 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.21/0.53  fof(f789,plain,(
% 0.21/0.53    ~spl4_8 | ~spl4_6 | ~spl4_54 | spl4_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f784,f196,f786,f118,f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl4_8 <=> v1_funct_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f784,plain,(
% 0.21/0.53    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_17),
% 0.21/0.53    inference(superposition,[],[f198,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f196])).
% 0.21/0.53  fof(f631,plain,(
% 0.21/0.53    ~spl4_6 | spl4_40 | ~spl4_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f623,f122,f627,f118])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    spl4_7 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.53  fof(f623,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.21/0.53    inference(superposition,[],[f75,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f122])).
% 0.21/0.53  fof(f606,plain,(
% 0.21/0.53    spl4_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f601])).
% 0.21/0.53  fof(f601,plain,(
% 0.21/0.53    $false | spl4_6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f53,f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f587,plain,(
% 0.21/0.53    spl4_33),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f582])).
% 0.21/0.53  fof(f582,plain,(
% 0.21/0.53    $false | spl4_33),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f53,f563,f66])).
% 0.21/0.53  fof(f563,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | spl4_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f561])).
% 0.21/0.53  fof(f550,plain,(
% 0.21/0.53    spl4_4 | ~spl4_12 | spl4_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f543,f122,f152,f102])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl4_12 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.53  fof(f543,plain,(
% 0.21/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f53,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f549,plain,(
% 0.21/0.53    ~spl4_8 | spl4_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f540,f148,f136])).
% 0.21/0.53  fof(f540,plain,(
% 0.21/0.53    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) | ~v1_funct_1(sK3)) )),
% 0.21/0.53    inference(resolution,[],[f53,f59])).
% 0.21/0.53  fof(f548,plain,(
% 0.21/0.53    ~spl4_8 | spl4_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f539,f144,f136])).
% 0.21/0.53  fof(f539,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.21/0.53    inference(resolution,[],[f53,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.53  fof(f393,plain,(
% 0.21/0.53    ~spl4_8 | ~spl4_30 | ~spl4_24 | spl4_2 | ~spl4_4 | ~spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f388,f106,f102,f93,f299,f390,f136])).
% 0.21/0.53  fof(f388,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK3) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.21/0.53    inference(forward_demodulation,[],[f369,f81])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK3) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.21/0.53    inference(superposition,[],[f349,f59])).
% 0.21/0.53  fof(f349,plain,(
% 0.21/0.53    ~v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.21/0.53    inference(forward_demodulation,[],[f348,f108])).
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.21/0.53    inference(forward_demodulation,[],[f218,f223])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 0.21/0.53    inference(backward_demodulation,[],[f95,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f102])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f93])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    ~spl4_4 | spl4_24),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f352])).
% 0.21/0.53  fof(f352,plain,(
% 0.21/0.53    $false | (~spl4_4 | spl4_24)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f220,f301])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl4_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f299])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_4),
% 0.21/0.53    inference(forward_demodulation,[],[f216,f81])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_4),
% 0.21/0.53    inference(backward_demodulation,[],[f53,f103])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    spl4_23 | ~spl4_24 | ~spl4_4 | ~spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f293,f106,f102,f299,f295])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5)),
% 0.21/0.53    inference(forward_demodulation,[],[f282,f81])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_4 | ~spl4_5)),
% 0.21/0.53    inference(resolution,[],[f246,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.21/0.53    inference(forward_demodulation,[],[f215,f108])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 0.21/0.53    inference(backward_demodulation,[],[f52,f103])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    spl4_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    $false | spl4_12),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f52,f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ~v1_funct_2(sK3,sK0,sK1) | spl4_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    spl4_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f205])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    $false | spl4_8),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f51,f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | spl4_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f136])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    ~spl4_8 | ~spl4_6 | spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f157,f89,f118,f136])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_1),
% 0.21/0.53    inference(resolution,[],[f91,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f89])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ~spl4_4 | spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f106,f102])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f56,f97,f93,f89])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (24666)------------------------------
% 0.21/0.53  % (24666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24666)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (24666)Memory used [KB]: 6652
% 0.21/0.53  % (24666)Time elapsed: 0.085 s
% 0.21/0.53  % (24666)------------------------------
% 0.21/0.53  % (24666)------------------------------
% 0.21/0.53  % (24652)Success in time 0.164 s
%------------------------------------------------------------------------------
