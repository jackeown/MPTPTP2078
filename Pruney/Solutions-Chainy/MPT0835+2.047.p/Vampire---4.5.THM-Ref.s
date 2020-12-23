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
% DateTime   : Thu Dec  3 12:57:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 250 expanded)
%              Number of leaves         :   30 (  99 expanded)
%              Depth                    :    8
%              Number of atoms          :  296 ( 582 expanded)
%              Number of equality atoms :   91 ( 183 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f66,f89,f97,f110,f120,f143,f183,f188,f193,f198,f236,f242,f260,f271,f272,f290,f295])).

fof(f295,plain,
    ( ~ spl3_1
    | ~ spl3_18
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_18
    | spl3_24 ),
    inference(subsumption_resolution,[],[f293,f240])).

fof(f240,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl3_18
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f293,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_1
    | spl3_24 ),
    inference(superposition,[],[f289,f60])).

fof(f60,plain,
    ( ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f289,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl3_24
  <=> k1_relat_1(sK2) = k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f290,plain,
    ( ~ spl3_24
    | ~ spl3_1
    | spl3_4
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f280,f180,f107,f86,f46,f287])).

fof(f86,plain,
    ( spl3_4
  <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f107,plain,
    ( spl3_7
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f180,plain,
    ( spl3_11
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f280,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | ~ spl3_1
    | spl3_4
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f279,f182])).

fof(f182,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f279,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | ~ spl3_1
    | spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f278,f58])).

fof(f58,plain,
    ( ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f278,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f88,f109])).

fof(f109,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f88,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f272,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f271,plain,
    ( spl3_22
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f223,f190,f268])).

fof(f268,plain,
    ( spl3_22
  <=> k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f190,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f223,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f206,f208])).

fof(f208,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f192,f40])).

fof(f192,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f190])).

fof(f206,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k1_relat_1(sK2))
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f192,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f260,plain,
    ( spl3_20
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f205,f190,f257])).

fof(f257,plain,
    ( spl3_20
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f205,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f192,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f242,plain,
    ( spl3_18
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f241,f233,f195,f238])).

fof(f195,plain,
    ( spl3_14
  <=> k1_relat_1(sK2) = k1_relset_1(sK1,k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f233,plain,
    ( spl3_17
  <=> k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f241,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f235,f197])).

fof(f197,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK1,k2_relat_1(sK2),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f195])).

fof(f235,plain,
    ( k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f233])).

fof(f236,plain,
    ( spl3_17
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f135,f117,f233])).

fof(f117,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f135,plain,
    ( k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f124,f126])).

fof(f126,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK1,k2_relat_1(sK2),sK2,X0)
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f119,f41])).

fof(f119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK2))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f124,plain,
    ( k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k8_relset_1(sK1,k2_relat_1(sK2),sK2,k2_relat_1(sK2))
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f119,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f198,plain,
    ( spl3_14
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f121,f117,f195])).

fof(f121,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK1,k2_relat_1(sK2),sK2)
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f119,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f193,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f98,f63,f190])).

fof(f63,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f43,f65,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f188,plain,
    ( ~ spl3_12
    | ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f145,f94,f46,f185])).

fof(f185,plain,
    ( spl3_12
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f94,plain,
    ( spl3_5
  <=> k2_relat_1(sK2) = k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f145,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_1
    | spl3_5 ),
    inference(superposition,[],[f96,f58])).

fof(f96,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f183,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f144,f140,f46,f180])).

fof(f140,plain,
    ( spl3_10
  <=> k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f144,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f58,f142])).

fof(f142,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f143,plain,
    ( spl3_10
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f71,f46,f140])).

fof(f71,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f69,f56])).

fof(f56,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f37])).

fof(f69,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f38])).

fof(f120,plain,
    ( spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f79,f46,f117])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK2))))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f43,f48,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f110,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f46,f107])).

fof(f54,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f36])).

fof(f97,plain,
    ( ~ spl3_5
    | ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f92,f82,f46,f94])).

fof(f82,plain,
    ( spl3_3
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f92,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2))
    | ~ spl3_1
    | spl3_3 ),
    inference(forward_demodulation,[],[f91,f76])).

fof(f76,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f75,f54])).

fof(f75,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f73,f60])).

fof(f73,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k8_relset_1(sK1,sK0,sK2,sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f39])).

fof(f91,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_1
    | spl3_3 ),
    inference(forward_demodulation,[],[f90,f60])).

fof(f90,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | ~ spl3_1
    | spl3_3 ),
    inference(forward_demodulation,[],[f84,f56])).

fof(f84,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f89,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f29,f86,f82])).

fof(f29,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f66,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f46,f63])).

fof(f50,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f31,f48,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f46])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:46:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (14809)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (14803)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (14798)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (14803)Refutation not found, incomplete strategy% (14803)------------------------------
% 0.21/0.50  % (14803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14803)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14803)Memory used [KB]: 6140
% 0.21/0.50  % (14803)Time elapsed: 0.096 s
% 0.21/0.50  % (14803)------------------------------
% 0.21/0.50  % (14803)------------------------------
% 0.21/0.50  % (14821)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (14801)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (14811)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (14813)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (14802)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (14810)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (14798)Refutation not found, incomplete strategy% (14798)------------------------------
% 0.21/0.51  % (14798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14798)Memory used [KB]: 10618
% 0.21/0.51  % (14798)Time elapsed: 0.094 s
% 0.21/0.51  % (14798)------------------------------
% 0.21/0.51  % (14798)------------------------------
% 0.21/0.51  % (14807)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (14821)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (14811)Refutation not found, incomplete strategy% (14811)------------------------------
% 0.21/0.51  % (14811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14811)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14811)Memory used [KB]: 6140
% 0.21/0.51  % (14819)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (14811)Time elapsed: 0.062 s
% 0.21/0.51  % (14811)------------------------------
% 0.21/0.51  % (14811)------------------------------
% 0.21/0.51  % (14815)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (14816)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (14800)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (14799)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (14817)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (14809)Refutation not found, incomplete strategy% (14809)------------------------------
% 0.21/0.51  % (14809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14809)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14809)Memory used [KB]: 10618
% 0.21/0.51  % (14809)Time elapsed: 0.108 s
% 0.21/0.51  % (14809)------------------------------
% 0.21/0.51  % (14809)------------------------------
% 0.21/0.51  % (14814)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (14806)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (14808)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (14823)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (14799)Refutation not found, incomplete strategy% (14799)------------------------------
% 0.21/0.52  % (14799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14799)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14799)Memory used [KB]: 10618
% 0.21/0.52  % (14799)Time elapsed: 0.110 s
% 0.21/0.52  % (14799)------------------------------
% 0.21/0.52  % (14799)------------------------------
% 0.21/0.52  % (14822)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (14818)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (14820)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (14804)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (14805)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (14804)Refutation not found, incomplete strategy% (14804)------------------------------
% 0.21/0.52  % (14804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14804)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14804)Memory used [KB]: 10618
% 0.21/0.52  % (14804)Time elapsed: 0.117 s
% 0.21/0.52  % (14804)------------------------------
% 0.21/0.52  % (14804)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f49,f66,f89,f97,f110,f120,f143,f183,f188,f193,f198,f236,f242,f260,f271,f272,f290,f295])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_18 | spl3_24),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f294])).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    $false | (~spl3_1 | ~spl3_18 | spl3_24)),
% 0.21/0.52    inference(subsumption_resolution,[],[f293,f240])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f238])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    spl3_18 <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.52  fof(f293,plain,(
% 0.21/0.52    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | (~spl3_1 | spl3_24)),
% 0.21/0.52    inference(superposition,[],[f289,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | spl3_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f287])).
% 0.21/0.52  fof(f287,plain,(
% 0.21/0.52    spl3_24 <=> k1_relat_1(sK2) = k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    ~spl3_24 | ~spl3_1 | spl3_4 | ~spl3_7 | ~spl3_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f280,f180,f107,f86,f46,f287])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl3_4 <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl3_7 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    spl3_11 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | (~spl3_1 | spl3_4 | ~spl3_7 | ~spl3_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f279,f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f180])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | (~spl3_1 | spl3_4 | ~spl3_7)),
% 0.21/0.52    inference(forward_demodulation,[],[f278,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) | (spl3_4 | ~spl3_7)),
% 0.21/0.52    inference(forward_demodulation,[],[f88,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    spl3_22 | ~spl3_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f223,f190,f268])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    spl3_22 <=> k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_13),
% 0.21/0.52    inference(forward_demodulation,[],[f206,f208])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)) ) | ~spl3_13),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f192,f40])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f190])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k1_relat_1(sK2)) | ~spl3_13),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f192,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    spl3_20 | ~spl3_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f205,f190,f257])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    spl3_20 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_13),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f192,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    spl3_18 | ~spl3_14 | ~spl3_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f241,f233,f195,f238])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    spl3_14 <=> k1_relat_1(sK2) = k1_relset_1(sK1,k2_relat_1(sK2),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    spl3_17 <=> k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | (~spl3_14 | ~spl3_17)),
% 0.21/0.52    inference(forward_demodulation,[],[f235,f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k1_relset_1(sK1,k2_relat_1(sK2),sK2) | ~spl3_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f195])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f233])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    spl3_17 | ~spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f135,f117,f233])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK2))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_9),
% 0.21/0.52    inference(forward_demodulation,[],[f124,f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK1,k2_relat_1(sK2),sK2,X0)) ) | ~spl3_9),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f119,f41])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK2)))) | ~spl3_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f117])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k8_relset_1(sK1,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) | ~spl3_9),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f119,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl3_14 | ~spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f121,f117,f195])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k1_relset_1(sK1,k2_relat_1(sK2),sK2) | ~spl3_9),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f119,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    spl3_13 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f98,f63,f190])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl3_2 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f43,f43,f65,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    ~spl3_12 | ~spl3_1 | spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f145,f94,f46,f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    spl3_12 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl3_5 <=> k2_relat_1(sK2) = k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | (~spl3_1 | spl3_5)),
% 0.21/0.52    inference(superposition,[],[f96,f58])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) | spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f94])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl3_11 | ~spl3_1 | ~spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f144,f140,f46,f180])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl3_10 <=> k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | (~spl3_1 | ~spl3_10)),
% 0.21/0.52    inference(superposition,[],[f58,f142])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) | ~spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f140])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl3_10 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f71,f46,f140])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) | ~spl3_1),
% 0.21/0.52    inference(forward_demodulation,[],[f69,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f37])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f38])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl3_9 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f79,f46,f117])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK2)))) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f43,f48,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl3_7 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f54,f46,f107])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f36])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~spl3_5 | ~spl3_1 | spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f92,f82,f46,f94])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl3_3 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) | (~spl3_1 | spl3_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f91,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | ~spl3_1),
% 0.21/0.52    inference(forward_demodulation,[],[f75,f54])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) | ~spl3_1),
% 0.21/0.52    inference(forward_demodulation,[],[f73,f60])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK0,sK2) = k8_relset_1(sK1,sK0,sK2,sK0) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f39])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | (~spl3_1 | spl3_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f90,f60])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | (~spl3_1 | spl3_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f84,f56])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~spl3_3 | ~spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f86,f82])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl3_2 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f46,f63])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f31,f48,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f46])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (14821)------------------------------
% 0.21/0.52  % (14821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14821)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (14821)Memory used [KB]: 10874
% 0.21/0.52  % (14821)Time elapsed: 0.063 s
% 0.21/0.52  % (14821)------------------------------
% 0.21/0.52  % (14821)------------------------------
% 0.21/0.53  % (14797)Success in time 0.163 s
%------------------------------------------------------------------------------
