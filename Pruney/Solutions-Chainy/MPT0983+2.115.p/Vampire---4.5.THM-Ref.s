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
% DateTime   : Thu Dec  3 13:01:51 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 611 expanded)
%              Number of leaves         :   33 ( 193 expanded)
%              Depth                    :   22
%              Number of atoms          :  553 (4054 expanded)
%              Number of equality atoms :   69 ( 135 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1428,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f157,f190,f1088,f1099,f1112,f1165,f1266,f1373,f1411])).

fof(f1411,plain,
    ( spl4_2
    | ~ spl4_57 ),
    inference(avatar_contradiction_clause,[],[f1410])).

fof(f1410,plain,
    ( $false
    | spl4_2
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f1409,f135])).

fof(f135,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f131,f81])).

fof(f81,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f131,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f79,f64])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f52,f51])).

fof(f51,plain,
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

fof(f52,plain,
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1409,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f1400,f119])).

fof(f119,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1400,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_57 ),
    inference(superposition,[],[f262,f1111])).

fof(f1111,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1109,plain,
    ( spl4_57
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f262,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f106,f210])).

fof(f210,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f84,f107])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
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

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f106,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f1373,plain,(
    spl4_56 ),
    inference(avatar_contradiction_clause,[],[f1372])).

fof(f1372,plain,
    ( $false
    | spl4_56 ),
    inference(subsumption_resolution,[],[f1371,f135])).

fof(f1371,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_56 ),
    inference(subsumption_resolution,[],[f1370,f249])).

fof(f249,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f94,f64])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1370,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_56 ),
    inference(resolution,[],[f1107,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1107,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_56 ),
    inference(avatar_component_clause,[],[f1105])).

fof(f1105,plain,
    ( spl4_56
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f1266,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f1265])).

fof(f1265,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1251,f122])).

fof(f122,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f103,f102])).

fof(f102,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f71,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f103,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f1251,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f115,f1178])).

fof(f1178,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f156,f198])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(resolution,[],[f147,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f147,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f156,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_6
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f115,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1165,plain,
    ( ~ spl4_4
    | spl4_5
    | ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f1164])).

fof(f1164,plain,
    ( $false
    | ~ spl4_4
    | spl4_5
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1140,f147])).

fof(f1140,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_5
    | ~ spl4_54 ),
    inference(backward_demodulation,[],[f169,f1083])).

fof(f1083,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1081,plain,
    ( spl4_54
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f169,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_5 ),
    inference(resolution,[],[f152,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f152,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_5
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1112,plain,
    ( ~ spl4_56
    | spl4_57 ),
    inference(avatar_split_clause,[],[f1103,f1109,f1105])).

fof(f1103,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f1102,f104])).

fof(f104,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f75,f71])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1102,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f1101,f104])).

fof(f1101,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1100,f135])).

fof(f1100,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1095,f134])).

fof(f134,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f130,f81])).

fof(f130,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f79,f61])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f1095,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f268,f1090])).

fof(f1090,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f1068,f1089])).

fof(f1089,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f1061,f307])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
      | k6_partfun1(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f97,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1061,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f65,f775])).

fof(f775,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f768,f59])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f768,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f335,f61])).

fof(f335,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k1_partfun1(X7,X8,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ v1_funct_1(X9) ) ),
    inference(subsumption_resolution,[],[f331,f62])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f331,plain,(
    ! [X8,X7,X9] :
      ( k1_partfun1(X7,X8,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X9) ) ),
    inference(resolution,[],[f99,f64])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f1068,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1067,f59])).

fof(f1067,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1066,f61])).

fof(f1066,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1065,f62])).

fof(f1065,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1062,f64])).

fof(f1062,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f101,f775])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f268,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f78,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1099,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f1098])).

fof(f1098,plain,
    ( $false
    | spl4_55 ),
    inference(subsumption_resolution,[],[f1091,f103])).

fof(f1091,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_55 ),
    inference(backward_demodulation,[],[f1087,f1090])).

fof(f1087,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f1085])).

fof(f1085,plain,
    ( spl4_55
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f1088,plain,
    ( spl4_54
    | ~ spl4_55
    | spl4_1 ),
    inference(avatar_split_clause,[],[f1079,f113,f1085,f1081])).

fof(f1079,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1078,f59])).

fof(f1078,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1077,f60])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f1077,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1076,f61])).

fof(f1076,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1075,f62])).

fof(f1075,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1074,f63])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f1074,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1073,f64])).

fof(f1073,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1064,f115])).

fof(f1064,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f95,f775])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f190,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f186,f146])).

fof(f146,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f186,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f170,f107])).

fof(f170,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f82,f69])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f157,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f138,f154,f150])).

fof(f138,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f80,f61])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f120,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f66,f117,f113])).

fof(f66,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.16/0.37  % Computer   : n024.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % WCLimit    : 600
% 0.16/0.37  % DateTime   : Tue Dec  1 13:31:51 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.23/0.53  % (14752)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.53  % (14756)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.53  % (14768)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.54  % (14748)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.54  % (14745)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (14760)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.54  % (14757)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.54  % (14762)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.55  % (14766)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.55  % (14754)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.55  % (14758)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.55  % (14746)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.55  % (14760)Refutation not found, incomplete strategy% (14760)------------------------------
% 0.23/0.55  % (14760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (14750)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.55  % (14749)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.55  % (14772)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.56  % (14764)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.56  % (14771)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.56  % (14744)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.56  % (14770)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.56  % (14747)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.56  % (14761)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.56  % (14760)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (14760)Memory used [KB]: 10746
% 0.23/0.56  % (14760)Time elapsed: 0.116 s
% 0.23/0.56  % (14760)------------------------------
% 0.23/0.56  % (14760)------------------------------
% 0.23/0.56  % (14765)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.57  % (14751)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.57  % (14763)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.57  % (14753)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.57  % (14759)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.57  % (14754)Refutation not found, incomplete strategy% (14754)------------------------------
% 0.23/0.57  % (14754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (14754)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (14754)Memory used [KB]: 10874
% 0.23/0.57  % (14754)Time elapsed: 0.122 s
% 0.23/0.57  % (14754)------------------------------
% 0.23/0.57  % (14754)------------------------------
% 0.23/0.57  % (14755)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.57  % (14773)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.58  % (14772)Refutation not found, incomplete strategy% (14772)------------------------------
% 0.23/0.58  % (14772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (14772)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (14772)Memory used [KB]: 10874
% 0.23/0.58  % (14772)Time elapsed: 0.134 s
% 0.23/0.58  % (14772)------------------------------
% 0.23/0.58  % (14772)------------------------------
% 0.23/0.58  % (14767)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.58  % (14769)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.63/0.61  % (14750)Refutation found. Thanks to Tanya!
% 1.63/0.61  % SZS status Theorem for theBenchmark
% 1.89/0.62  % SZS output start Proof for theBenchmark
% 1.89/0.62  fof(f1428,plain,(
% 1.89/0.62    $false),
% 1.89/0.62    inference(avatar_sat_refutation,[],[f120,f157,f190,f1088,f1099,f1112,f1165,f1266,f1373,f1411])).
% 1.89/0.62  fof(f1411,plain,(
% 1.89/0.62    spl4_2 | ~spl4_57),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f1410])).
% 1.89/0.62  fof(f1410,plain,(
% 1.89/0.62    $false | (spl4_2 | ~spl4_57)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1409,f135])).
% 1.89/0.62  fof(f135,plain,(
% 1.89/0.62    v1_relat_1(sK3)),
% 1.89/0.62    inference(subsumption_resolution,[],[f131,f81])).
% 1.89/0.62  fof(f81,plain,(
% 1.89/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f11])).
% 1.89/0.62  fof(f11,axiom,(
% 1.89/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.89/0.62  fof(f131,plain,(
% 1.89/0.62    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.89/0.62    inference(resolution,[],[f79,f64])).
% 1.89/0.62  fof(f64,plain,(
% 1.89/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.89/0.62    inference(cnf_transformation,[],[f53])).
% 1.89/0.62  fof(f53,plain,(
% 1.89/0.62    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f52,f51])).
% 1.89/0.62  fof(f51,plain,(
% 1.89/0.62    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f52,plain,(
% 1.89/0.62    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f28,plain,(
% 1.89/0.62    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.89/0.62    inference(flattening,[],[f27])).
% 1.89/0.62  fof(f27,plain,(
% 1.89/0.62    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.89/0.62    inference(ennf_transformation,[],[f26])).
% 1.89/0.62  fof(f26,negated_conjecture,(
% 1.89/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.89/0.62    inference(negated_conjecture,[],[f25])).
% 1.89/0.62  fof(f25,conjecture,(
% 1.89/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.89/0.62  fof(f79,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f32])).
% 1.89/0.62  fof(f32,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f9])).
% 1.89/0.62  fof(f9,axiom,(
% 1.89/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.89/0.62  fof(f1409,plain,(
% 1.89/0.62    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_57)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1400,f119])).
% 1.89/0.62  fof(f119,plain,(
% 1.89/0.62    ~v2_funct_2(sK3,sK0) | spl4_2),
% 1.89/0.62    inference(avatar_component_clause,[],[f117])).
% 1.89/0.62  fof(f117,plain,(
% 1.89/0.62    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.89/0.62  fof(f1400,plain,(
% 1.89/0.62    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_57),
% 1.89/0.62    inference(superposition,[],[f262,f1111])).
% 1.89/0.62  fof(f1111,plain,(
% 1.89/0.62    sK0 = k2_relat_1(sK3) | ~spl4_57),
% 1.89/0.62    inference(avatar_component_clause,[],[f1109])).
% 1.89/0.62  fof(f1109,plain,(
% 1.89/0.62    spl4_57 <=> sK0 = k2_relat_1(sK3)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.89/0.62  fof(f262,plain,(
% 1.89/0.62    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f106,f210])).
% 1.89/0.62  fof(f210,plain,(
% 1.89/0.62    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.89/0.62    inference(resolution,[],[f84,f107])).
% 1.89/0.62  fof(f107,plain,(
% 1.89/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.89/0.62    inference(equality_resolution,[],[f90])).
% 1.89/0.62  fof(f90,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.89/0.62    inference(cnf_transformation,[],[f57])).
% 1.89/0.62  fof(f57,plain,(
% 1.89/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.62    inference(flattening,[],[f56])).
% 1.89/0.62  fof(f56,plain,(
% 1.89/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.62    inference(nnf_transformation,[],[f1])).
% 1.89/0.62  fof(f1,axiom,(
% 1.89/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.89/0.62  fof(f84,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f54])).
% 1.89/0.62  fof(f54,plain,(
% 1.89/0.62    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.89/0.62    inference(nnf_transformation,[],[f36])).
% 1.89/0.62  fof(f36,plain,(
% 1.89/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.89/0.62    inference(ennf_transformation,[],[f10])).
% 1.89/0.62  fof(f10,axiom,(
% 1.89/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.89/0.62  fof(f106,plain,(
% 1.89/0.62    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.89/0.62    inference(equality_resolution,[],[f88])).
% 1.89/0.62  fof(f88,plain,(
% 1.89/0.62    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f55])).
% 1.89/0.62  fof(f55,plain,(
% 1.89/0.62    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.89/0.62    inference(nnf_transformation,[],[f40])).
% 1.89/0.62  fof(f40,plain,(
% 1.89/0.62    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.89/0.62    inference(flattening,[],[f39])).
% 1.89/0.62  fof(f39,plain,(
% 1.89/0.62    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.89/0.62    inference(ennf_transformation,[],[f19])).
% 1.89/0.62  fof(f19,axiom,(
% 1.89/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.89/0.62  fof(f1373,plain,(
% 1.89/0.62    spl4_56),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f1372])).
% 1.89/0.62  fof(f1372,plain,(
% 1.89/0.62    $false | spl4_56),
% 1.89/0.62    inference(subsumption_resolution,[],[f1371,f135])).
% 1.89/0.62  fof(f1371,plain,(
% 1.89/0.62    ~v1_relat_1(sK3) | spl4_56),
% 1.89/0.62    inference(subsumption_resolution,[],[f1370,f249])).
% 1.89/0.62  fof(f249,plain,(
% 1.89/0.62    v5_relat_1(sK3,sK0)),
% 1.89/0.62    inference(resolution,[],[f94,f64])).
% 1.89/0.62  fof(f94,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f42])).
% 1.89/0.62  fof(f42,plain,(
% 1.89/0.62    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.62    inference(ennf_transformation,[],[f17])).
% 1.89/0.62  fof(f17,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.89/0.62  fof(f1370,plain,(
% 1.89/0.62    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl4_56),
% 1.89/0.62    inference(resolution,[],[f1107,f83])).
% 1.89/0.62  fof(f83,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f54])).
% 1.89/0.62  fof(f1107,plain,(
% 1.89/0.62    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_56),
% 1.89/0.62    inference(avatar_component_clause,[],[f1105])).
% 1.89/0.62  fof(f1105,plain,(
% 1.89/0.62    spl4_56 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 1.89/0.62  fof(f1266,plain,(
% 1.89/0.62    spl4_1 | ~spl4_4 | ~spl4_6),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f1265])).
% 1.89/0.62  fof(f1265,plain,(
% 1.89/0.62    $false | (spl4_1 | ~spl4_4 | ~spl4_6)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1251,f122])).
% 1.89/0.62  fof(f122,plain,(
% 1.89/0.62    v2_funct_1(k1_xboole_0)),
% 1.89/0.62    inference(superposition,[],[f103,f102])).
% 1.89/0.62  fof(f102,plain,(
% 1.89/0.62    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.89/0.62    inference(definition_unfolding,[],[f67,f71])).
% 1.89/0.62  fof(f71,plain,(
% 1.89/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f23])).
% 1.89/0.62  fof(f23,axiom,(
% 1.89/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.89/0.62  fof(f67,plain,(
% 1.89/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.89/0.62    inference(cnf_transformation,[],[f15])).
% 1.89/0.62  fof(f15,axiom,(
% 1.89/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.89/0.62  fof(f103,plain,(
% 1.89/0.62    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.89/0.62    inference(definition_unfolding,[],[f68,f71])).
% 1.89/0.62  fof(f68,plain,(
% 1.89/0.62    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f16])).
% 1.89/0.62  fof(f16,axiom,(
% 1.89/0.62    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 1.89/0.62  fof(f1251,plain,(
% 1.89/0.62    ~v2_funct_1(k1_xboole_0) | (spl4_1 | ~spl4_4 | ~spl4_6)),
% 1.89/0.62    inference(backward_demodulation,[],[f115,f1178])).
% 1.89/0.62  fof(f1178,plain,(
% 1.89/0.62    k1_xboole_0 = sK2 | (~spl4_4 | ~spl4_6)),
% 1.89/0.62    inference(resolution,[],[f156,f198])).
% 1.89/0.62  fof(f198,plain,(
% 1.89/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_4),
% 1.89/0.62    inference(resolution,[],[f147,f92])).
% 1.89/0.62  fof(f92,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f41])).
% 1.89/0.62  fof(f41,plain,(
% 1.89/0.62    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f5])).
% 1.89/0.62  fof(f5,axiom,(
% 1.89/0.62    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.89/0.62  fof(f147,plain,(
% 1.89/0.62    v1_xboole_0(k1_xboole_0) | ~spl4_4),
% 1.89/0.62    inference(avatar_component_clause,[],[f145])).
% 1.89/0.62  fof(f145,plain,(
% 1.89/0.62    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.89/0.62  fof(f156,plain,(
% 1.89/0.62    v1_xboole_0(sK2) | ~spl4_6),
% 1.89/0.62    inference(avatar_component_clause,[],[f154])).
% 1.89/0.62  fof(f154,plain,(
% 1.89/0.62    spl4_6 <=> v1_xboole_0(sK2)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.89/0.62  fof(f115,plain,(
% 1.89/0.62    ~v2_funct_1(sK2) | spl4_1),
% 1.89/0.62    inference(avatar_component_clause,[],[f113])).
% 1.89/0.62  fof(f113,plain,(
% 1.89/0.62    spl4_1 <=> v2_funct_1(sK2)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.89/0.62  fof(f1165,plain,(
% 1.89/0.62    ~spl4_4 | spl4_5 | ~spl4_54),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f1164])).
% 1.89/0.62  fof(f1164,plain,(
% 1.89/0.62    $false | (~spl4_4 | spl4_5 | ~spl4_54)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1140,f147])).
% 1.89/0.62  fof(f1140,plain,(
% 1.89/0.62    ~v1_xboole_0(k1_xboole_0) | (spl4_5 | ~spl4_54)),
% 1.89/0.62    inference(backward_demodulation,[],[f169,f1083])).
% 1.89/0.62  fof(f1083,plain,(
% 1.89/0.62    k1_xboole_0 = sK0 | ~spl4_54),
% 1.89/0.62    inference(avatar_component_clause,[],[f1081])).
% 1.89/0.62  fof(f1081,plain,(
% 1.89/0.62    spl4_54 <=> k1_xboole_0 = sK0),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.89/0.62  fof(f169,plain,(
% 1.89/0.62    ~v1_xboole_0(sK0) | spl4_5),
% 1.89/0.62    inference(resolution,[],[f152,f85])).
% 1.89/0.62  fof(f85,plain,(
% 1.89/0.62    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f37])).
% 1.89/0.62  fof(f37,plain,(
% 1.89/0.62    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f7])).
% 1.89/0.62  fof(f7,axiom,(
% 1.89/0.62    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.89/0.62  fof(f152,plain,(
% 1.89/0.62    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_5),
% 1.89/0.62    inference(avatar_component_clause,[],[f150])).
% 1.89/0.62  fof(f150,plain,(
% 1.89/0.62    spl4_5 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.89/0.62  fof(f1112,plain,(
% 1.89/0.62    ~spl4_56 | spl4_57),
% 1.89/0.62    inference(avatar_split_clause,[],[f1103,f1109,f1105])).
% 1.89/0.63  fof(f1103,plain,(
% 1.89/0.63    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0)),
% 1.89/0.63    inference(forward_demodulation,[],[f1102,f104])).
% 1.89/0.63  fof(f104,plain,(
% 1.89/0.63    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.89/0.63    inference(definition_unfolding,[],[f75,f71])).
% 1.89/0.63  fof(f75,plain,(
% 1.89/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.89/0.63    inference(cnf_transformation,[],[f14])).
% 1.89/0.63  fof(f14,axiom,(
% 1.89/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.89/0.63  fof(f1102,plain,(
% 1.89/0.63    ~r1_tarski(k2_relat_1(sK3),sK0) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.89/0.63    inference(forward_demodulation,[],[f1101,f104])).
% 1.89/0.63  fof(f1101,plain,(
% 1.89/0.63    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.89/0.63    inference(subsumption_resolution,[],[f1100,f135])).
% 1.89/0.63  fof(f1100,plain,(
% 1.89/0.63    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.89/0.63    inference(subsumption_resolution,[],[f1095,f134])).
% 1.89/0.63  fof(f134,plain,(
% 1.89/0.63    v1_relat_1(sK2)),
% 1.89/0.63    inference(subsumption_resolution,[],[f130,f81])).
% 1.89/0.63  fof(f130,plain,(
% 1.89/0.63    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.89/0.63    inference(resolution,[],[f79,f61])).
% 1.89/0.63  fof(f61,plain,(
% 1.89/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.89/0.63    inference(cnf_transformation,[],[f53])).
% 1.89/0.63  fof(f1095,plain,(
% 1.89/0.63    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.89/0.63    inference(superposition,[],[f268,f1090])).
% 1.89/0.63  fof(f1090,plain,(
% 1.89/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.89/0.63    inference(global_subsumption,[],[f1068,f1089])).
% 1.89/0.63  fof(f1089,plain,(
% 1.89/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.89/0.63    inference(resolution,[],[f1061,f307])).
% 1.89/0.63  fof(f307,plain,(
% 1.89/0.63    ( ! [X0,X1] : (~r2_relset_1(X0,X0,X1,k6_partfun1(X0)) | k6_partfun1(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.89/0.63    inference(resolution,[],[f97,f73])).
% 1.89/0.63  fof(f73,plain,(
% 1.89/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.89/0.63    inference(cnf_transformation,[],[f21])).
% 1.89/0.63  fof(f21,axiom,(
% 1.89/0.63    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.89/0.63  fof(f97,plain,(
% 1.89/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.89/0.63    inference(cnf_transformation,[],[f58])).
% 1.89/0.63  fof(f58,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.63    inference(nnf_transformation,[],[f46])).
% 1.89/0.63  fof(f46,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.89/0.63    inference(flattening,[],[f45])).
% 1.89/0.63  fof(f45,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.89/0.63    inference(ennf_transformation,[],[f18])).
% 1.89/0.63  fof(f18,axiom,(
% 1.89/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.89/0.63  fof(f1061,plain,(
% 1.89/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.89/0.63    inference(backward_demodulation,[],[f65,f775])).
% 1.89/0.63  fof(f775,plain,(
% 1.89/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.89/0.63    inference(subsumption_resolution,[],[f768,f59])).
% 1.89/0.63  fof(f59,plain,(
% 1.89/0.63    v1_funct_1(sK2)),
% 1.89/0.63    inference(cnf_transformation,[],[f53])).
% 1.89/0.63  fof(f768,plain,(
% 1.89/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.89/0.63    inference(resolution,[],[f335,f61])).
% 1.89/0.63  fof(f335,plain,(
% 1.89/0.63    ( ! [X8,X7,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k1_partfun1(X7,X8,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3) | ~v1_funct_1(X9)) )),
% 1.89/0.63    inference(subsumption_resolution,[],[f331,f62])).
% 1.89/0.63  fof(f62,plain,(
% 1.89/0.63    v1_funct_1(sK3)),
% 1.89/0.63    inference(cnf_transformation,[],[f53])).
% 1.89/0.63  fof(f331,plain,(
% 1.89/0.63    ( ! [X8,X7,X9] : (k1_partfun1(X7,X8,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X9)) )),
% 1.89/0.63    inference(resolution,[],[f99,f64])).
% 1.89/0.63  fof(f99,plain,(
% 1.89/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f48])).
% 1.89/0.63  fof(f48,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.89/0.63    inference(flattening,[],[f47])).
% 1.89/0.63  fof(f47,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.89/0.63    inference(ennf_transformation,[],[f22])).
% 1.89/0.63  fof(f22,axiom,(
% 1.89/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.89/0.63  fof(f65,plain,(
% 1.89/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.89/0.63    inference(cnf_transformation,[],[f53])).
% 1.89/0.63  fof(f1068,plain,(
% 1.89/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.89/0.63    inference(subsumption_resolution,[],[f1067,f59])).
% 1.89/0.63  fof(f1067,plain,(
% 1.89/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.89/0.63    inference(subsumption_resolution,[],[f1066,f61])).
% 1.89/0.63  fof(f1066,plain,(
% 1.89/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.89/0.63    inference(subsumption_resolution,[],[f1065,f62])).
% 1.89/0.63  fof(f1065,plain,(
% 1.89/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.89/0.63    inference(subsumption_resolution,[],[f1062,f64])).
% 1.89/0.63  fof(f1062,plain,(
% 1.89/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.89/0.63    inference(superposition,[],[f101,f775])).
% 1.89/0.63  fof(f101,plain,(
% 1.89/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f50])).
% 1.89/0.63  fof(f50,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.89/0.63    inference(flattening,[],[f49])).
% 1.89/0.63  fof(f49,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.89/0.63    inference(ennf_transformation,[],[f20])).
% 1.89/0.63  fof(f20,axiom,(
% 1.89/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.89/0.63  fof(f268,plain,(
% 1.89/0.63    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.89/0.63    inference(resolution,[],[f78,f91])).
% 1.89/0.63  fof(f91,plain,(
% 1.89/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f57])).
% 1.89/0.63  fof(f78,plain,(
% 1.89/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f31])).
% 1.89/0.63  fof(f31,plain,(
% 1.89/0.63    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.89/0.63    inference(ennf_transformation,[],[f12])).
% 1.89/0.63  fof(f12,axiom,(
% 1.89/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.89/0.63  fof(f1099,plain,(
% 1.89/0.63    spl4_55),
% 1.89/0.63    inference(avatar_contradiction_clause,[],[f1098])).
% 1.89/0.63  fof(f1098,plain,(
% 1.89/0.63    $false | spl4_55),
% 1.89/0.63    inference(subsumption_resolution,[],[f1091,f103])).
% 1.89/0.63  fof(f1091,plain,(
% 1.89/0.63    ~v2_funct_1(k6_partfun1(sK0)) | spl4_55),
% 1.89/0.63    inference(backward_demodulation,[],[f1087,f1090])).
% 1.89/0.63  fof(f1087,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_55),
% 1.89/0.63    inference(avatar_component_clause,[],[f1085])).
% 1.89/0.63  fof(f1085,plain,(
% 1.89/0.63    spl4_55 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.89/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.89/0.63  fof(f1088,plain,(
% 1.89/0.63    spl4_54 | ~spl4_55 | spl4_1),
% 1.89/0.63    inference(avatar_split_clause,[],[f1079,f113,f1085,f1081])).
% 1.89/0.63  fof(f1079,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | spl4_1),
% 1.89/0.63    inference(subsumption_resolution,[],[f1078,f59])).
% 1.89/0.63  fof(f1078,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | spl4_1),
% 1.89/0.63    inference(subsumption_resolution,[],[f1077,f60])).
% 1.89/0.63  fof(f60,plain,(
% 1.89/0.63    v1_funct_2(sK2,sK0,sK1)),
% 1.89/0.63    inference(cnf_transformation,[],[f53])).
% 1.89/0.63  fof(f1077,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.89/0.63    inference(subsumption_resolution,[],[f1076,f61])).
% 1.89/0.63  fof(f1076,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.89/0.63    inference(subsumption_resolution,[],[f1075,f62])).
% 1.89/0.63  fof(f1075,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.89/0.63    inference(subsumption_resolution,[],[f1074,f63])).
% 1.89/0.63  fof(f63,plain,(
% 1.89/0.63    v1_funct_2(sK3,sK1,sK0)),
% 1.89/0.63    inference(cnf_transformation,[],[f53])).
% 1.89/0.63  fof(f1074,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.89/0.63    inference(subsumption_resolution,[],[f1073,f64])).
% 1.89/0.63  fof(f1073,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.89/0.63    inference(subsumption_resolution,[],[f1064,f115])).
% 1.89/0.63  fof(f1064,plain,(
% 1.89/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.89/0.63    inference(superposition,[],[f95,f775])).
% 1.89/0.63  fof(f95,plain,(
% 1.89/0.63    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f44])).
% 1.89/0.63  fof(f44,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.89/0.63    inference(flattening,[],[f43])).
% 1.89/0.63  fof(f43,plain,(
% 1.89/0.63    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.89/0.63    inference(ennf_transformation,[],[f24])).
% 1.89/0.63  fof(f24,axiom,(
% 1.89/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.89/0.63  fof(f190,plain,(
% 1.89/0.63    spl4_4),
% 1.89/0.63    inference(avatar_contradiction_clause,[],[f189])).
% 1.89/0.63  fof(f189,plain,(
% 1.89/0.63    $false | spl4_4),
% 1.89/0.63    inference(subsumption_resolution,[],[f186,f146])).
% 1.89/0.63  fof(f146,plain,(
% 1.89/0.63    ~v1_xboole_0(k1_xboole_0) | spl4_4),
% 1.89/0.63    inference(avatar_component_clause,[],[f145])).
% 1.89/0.63  fof(f186,plain,(
% 1.89/0.63    v1_xboole_0(k1_xboole_0)),
% 1.89/0.63    inference(resolution,[],[f170,f107])).
% 1.89/0.63  fof(f170,plain,(
% 1.89/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.89/0.63    inference(resolution,[],[f82,f69])).
% 1.89/0.63  fof(f69,plain,(
% 1.89/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f3])).
% 1.89/0.63  fof(f3,axiom,(
% 1.89/0.63    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.89/0.63  fof(f82,plain,(
% 1.89/0.63    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f35])).
% 1.89/0.63  fof(f35,plain,(
% 1.89/0.63    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.89/0.63    inference(flattening,[],[f34])).
% 1.89/0.63  fof(f34,plain,(
% 1.89/0.63    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.89/0.63    inference(ennf_transformation,[],[f4])).
% 1.89/0.63  fof(f4,axiom,(
% 1.89/0.63    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.89/0.63  fof(f157,plain,(
% 1.89/0.63    ~spl4_5 | spl4_6),
% 1.89/0.63    inference(avatar_split_clause,[],[f138,f154,f150])).
% 1.89/0.63  fof(f138,plain,(
% 1.89/0.63    v1_xboole_0(sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.89/0.63    inference(resolution,[],[f80,f61])).
% 1.89/0.63  fof(f80,plain,(
% 1.89/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f33])).
% 1.89/0.63  fof(f33,plain,(
% 1.89/0.63    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.89/0.63    inference(ennf_transformation,[],[f8])).
% 1.89/0.63  fof(f8,axiom,(
% 1.89/0.63    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.89/0.63  fof(f120,plain,(
% 1.89/0.63    ~spl4_1 | ~spl4_2),
% 1.89/0.63    inference(avatar_split_clause,[],[f66,f117,f113])).
% 1.89/0.63  fof(f66,plain,(
% 1.89/0.63    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.89/0.63    inference(cnf_transformation,[],[f53])).
% 1.89/0.63  % SZS output end Proof for theBenchmark
% 1.89/0.63  % (14750)------------------------------
% 1.89/0.63  % (14750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.63  % (14750)Termination reason: Refutation
% 1.89/0.63  
% 1.89/0.63  % (14750)Memory used [KB]: 11513
% 1.89/0.63  % (14750)Time elapsed: 0.138 s
% 1.89/0.63  % (14750)------------------------------
% 1.89/0.63  % (14750)------------------------------
% 1.89/0.63  % (14743)Success in time 0.245 s
%------------------------------------------------------------------------------
