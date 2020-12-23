%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 592 expanded)
%              Number of leaves         :   26 ( 152 expanded)
%              Depth                    :   16
%              Number of atoms          :  469 (3080 expanded)
%              Number of equality atoms :  125 ( 879 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f876,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f118,f132,f452,f464,f484,f518,f547,f642,f664,f785,f867])).

fof(f867,plain,
    ( spl5_2
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f866])).

fof(f866,plain,
    ( $false
    | spl5_2
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f865,f471])).

fof(f471,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f470])).

fof(f470,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f272,f274])).

fof(f274,plain,(
    ! [X8,X9] : k1_xboole_0 = k1_relset_1(X8,X9,k1_xboole_0) ),
    inference(forward_demodulation,[],[f269,f260])).

fof(f260,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f134,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f134,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f61,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f269,plain,(
    ! [X8,X9] : k1_relat_1(k1_xboole_0) = k1_relset_1(X8,X9,k1_xboole_0) ),
    inference(resolution,[],[f142,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f142,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f73,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f272,plain,(
    ! [X13] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X13,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X13) ) ),
    inference(resolution,[],[f142,f129])).

fof(f129,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f95,f91])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f38])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f865,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f695,f774])).

fof(f774,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f773,f91])).

fof(f773,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))
    | ~ spl5_5
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f483,f117])).

fof(f117,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f483,plain,
    ( sK3 = k2_zfmisc_1(sK0,k2_relat_1(sK3))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl5_27
  <=> sK3 = k2_zfmisc_1(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f695,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f104,f117])).

fof(f104,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f785,plain,
    ( ~ spl5_5
    | spl5_8
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | ~ spl5_5
    | spl5_8
    | ~ spl5_27 ),
    inference(global_subsumption,[],[f156,f774])).

fof(f156,plain,
    ( k1_xboole_0 != sK3
    | spl5_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_8
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f664,plain,
    ( ~ spl5_3
    | spl5_8
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f663])).

fof(f663,plain,
    ( $false
    | ~ spl5_3
    | spl5_8
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f662,f58])).

fof(f662,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_3
    | spl5_8
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f658,f156])).

fof(f658,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_3
    | ~ spl5_28 ),
    inference(resolution,[],[f656,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f656,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f655,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f655,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl5_3
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f651,f532])).

fof(f532,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl5_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f651,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f107,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f642,plain,
    ( ~ spl5_5
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f641])).

fof(f641,plain,
    ( $false
    | ~ spl5_5
    | spl5_26 ),
    inference(subsumption_resolution,[],[f640,f58])).

fof(f640,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_5
    | spl5_26 ),
    inference(forward_demodulation,[],[f613,f91])).

fof(f613,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)),sK3)
    | ~ spl5_5
    | spl5_26 ),
    inference(superposition,[],[f479,f117])).

fof(f479,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k2_relat_1(sK3)),sK3)
    | spl5_26 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl5_26
  <=> r1_tarski(k2_zfmisc_1(sK0,k2_relat_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f547,plain,
    ( spl5_2
    | spl5_4
    | spl5_28 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | spl5_2
    | spl5_4
    | spl5_28 ),
    inference(global_subsumption,[],[f528,f538,f531])).

fof(f531,plain,
    ( k1_xboole_0 != sK2
    | spl5_28 ),
    inference(avatar_component_clause,[],[f530])).

fof(f538,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl5_4 ),
    inference(forward_demodulation,[],[f522,f257])).

fof(f257,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl5_4 ),
    inference(superposition,[],[f203,f213])).

fof(f213,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f212,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK1
    | spl5_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f212,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f208,f52])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f208,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f203,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f79,f53])).

fof(f522,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | spl5_4 ),
    inference(resolution,[],[f516,f79])).

fof(f516,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_4 ),
    inference(resolution,[],[f350,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | spl5_4 ),
    inference(forward_demodulation,[],[f349,f257])).

fof(f349,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f346,f146])).

fof(f146,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f144,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f144,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f64,f53])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f346,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f256,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f256,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(superposition,[],[f54,f199])).

fof(f199,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f78,f53])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f528,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f520,f104])).

fof(f520,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | spl5_4 ),
    inference(resolution,[],[f516,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f518,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f516,f108])).

fof(f108,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f484,plain,
    ( ~ spl5_26
    | spl5_27 ),
    inference(avatar_split_clause,[],[f474,f481,f477])).

fof(f474,plain,
    ( sK3 = k2_zfmisc_1(sK0,k2_relat_1(sK3))
    | ~ r1_tarski(k2_zfmisc_1(sK0,k2_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f400,f71])).

fof(f400,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,k2_relat_1(sK3))) ),
    inference(resolution,[],[f345,f72])).

fof(f345,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK3)))) ),
    inference(subsumption_resolution,[],[f343,f146])).

fof(f343,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f207,f196])).

fof(f196,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f195,f146])).

fof(f195,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f181,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f181,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f80,f53])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f77,f88])).

fof(f464,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl5_4
    | spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f462,f116])).

fof(f116,plain,
    ( k1_xboole_0 != sK0
    | spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f462,plain,
    ( k1_xboole_0 = sK0
    | spl5_4
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f448,f260])).

fof(f448,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f257,f157])).

fof(f157,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f452,plain,
    ( spl5_3
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f430,f142])).

fof(f430,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_3
    | ~ spl5_8 ),
    inference(superposition,[],[f108,f157])).

fof(f132,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f118,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f55,f115,f111])).

fof(f55,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f56,f106,f102,f98])).

fof(f56,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (10740)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (10722)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (10723)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (10743)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (10723)Refutation not found, incomplete strategy% (10723)------------------------------
% 0.22/0.51  % (10723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10723)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (10723)Memory used [KB]: 10618
% 0.22/0.51  % (10723)Time elapsed: 0.084 s
% 0.22/0.51  % (10723)------------------------------
% 0.22/0.51  % (10723)------------------------------
% 0.22/0.51  % (10732)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (10742)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (10741)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (10732)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (10728)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (10734)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (10730)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (10729)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (10733)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (10728)Refutation not found, incomplete strategy% (10728)------------------------------
% 0.22/0.52  % (10728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10728)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10728)Memory used [KB]: 10618
% 0.22/0.52  % (10728)Time elapsed: 0.109 s
% 0.22/0.52  % (10728)------------------------------
% 0.22/0.52  % (10728)------------------------------
% 1.34/0.53  % (10727)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.34/0.53  % (10739)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.34/0.53  % (10731)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.34/0.53  % (10747)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.34/0.53  % (10745)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.34/0.53  % (10735)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f876,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f109,f118,f132,f452,f464,f484,f518,f547,f642,f664,f785,f867])).
% 1.34/0.53  fof(f867,plain,(
% 1.34/0.53    spl5_2 | ~spl5_5 | ~spl5_27),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f866])).
% 1.34/0.53  fof(f866,plain,(
% 1.34/0.53    $false | (spl5_2 | ~spl5_5 | ~spl5_27)),
% 1.34/0.53    inference(subsumption_resolution,[],[f865,f471])).
% 1.34/0.53  fof(f471,plain,(
% 1.34/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f470])).
% 1.34/0.53  fof(f470,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.34/0.53    inference(superposition,[],[f272,f274])).
% 1.34/0.53  fof(f274,plain,(
% 1.34/0.53    ( ! [X8,X9] : (k1_xboole_0 = k1_relset_1(X8,X9,k1_xboole_0)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f269,f260])).
% 1.34/0.53  fof(f260,plain,(
% 1.34/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.34/0.53    inference(resolution,[],[f134,f60])).
% 1.34/0.53  fof(f60,plain,(
% 1.34/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.34/0.53  fof(f134,plain,(
% 1.34/0.53    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 1.34/0.53    inference(resolution,[],[f61,f57])).
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    v1_xboole_0(k1_xboole_0)),
% 1.34/0.53    inference(cnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    v1_xboole_0(k1_xboole_0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.34/0.53  fof(f61,plain,(
% 1.34/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.34/0.53    inference(ennf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,axiom,(
% 1.34/0.53    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.34/0.53  fof(f269,plain,(
% 1.34/0.53    ( ! [X8,X9] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X8,X9,k1_xboole_0)) )),
% 1.34/0.53    inference(resolution,[],[f142,f79])).
% 1.34/0.53  fof(f79,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f35])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.34/0.53  fof(f142,plain,(
% 1.34/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.34/0.53    inference(resolution,[],[f73,f58])).
% 1.34/0.53  fof(f58,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.34/0.53  fof(f73,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f47])).
% 1.34/0.53  fof(f47,plain,(
% 1.34/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.34/0.53    inference(nnf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.34/0.53  fof(f272,plain,(
% 1.34/0.53    ( ! [X13] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X13,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X13)) )),
% 1.34/0.53    inference(resolution,[],[f142,f129])).
% 1.34/0.53  fof(f129,plain,(
% 1.34/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f95,f91])).
% 1.34/0.53  fof(f91,plain,(
% 1.34/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.34/0.53    inference(equality_resolution,[],[f75])).
% 1.34/0.53  fof(f75,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f49])).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.34/0.53    inference(flattening,[],[f48])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.34/0.53    inference(nnf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.34/0.53  fof(f95,plain,(
% 1.34/0.53    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.34/0.53    inference(equality_resolution,[],[f84])).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f50])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(nnf_transformation,[],[f38])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(flattening,[],[f37])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f19])).
% 1.34/0.53  fof(f19,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.34/0.53  fof(f865,plain,(
% 1.34/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (spl5_2 | ~spl5_5 | ~spl5_27)),
% 1.34/0.53    inference(forward_demodulation,[],[f695,f774])).
% 1.34/0.53  fof(f774,plain,(
% 1.34/0.53    k1_xboole_0 = sK3 | (~spl5_5 | ~spl5_27)),
% 1.34/0.53    inference(forward_demodulation,[],[f773,f91])).
% 1.34/0.53  fof(f773,plain,(
% 1.34/0.53    sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) | (~spl5_5 | ~spl5_27)),
% 1.34/0.53    inference(forward_demodulation,[],[f483,f117])).
% 1.34/0.53  fof(f117,plain,(
% 1.34/0.53    k1_xboole_0 = sK0 | ~spl5_5),
% 1.34/0.53    inference(avatar_component_clause,[],[f115])).
% 1.34/0.53  fof(f115,plain,(
% 1.34/0.53    spl5_5 <=> k1_xboole_0 = sK0),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.34/0.53  fof(f483,plain,(
% 1.34/0.53    sK3 = k2_zfmisc_1(sK0,k2_relat_1(sK3)) | ~spl5_27),
% 1.34/0.53    inference(avatar_component_clause,[],[f481])).
% 1.34/0.53  fof(f481,plain,(
% 1.34/0.53    spl5_27 <=> sK3 = k2_zfmisc_1(sK0,k2_relat_1(sK3))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.34/0.53  fof(f695,plain,(
% 1.34/0.53    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl5_2 | ~spl5_5)),
% 1.34/0.53    inference(superposition,[],[f104,f117])).
% 1.34/0.53  fof(f104,plain,(
% 1.34/0.53    ~v1_funct_2(sK3,sK0,sK2) | spl5_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f102])).
% 1.34/0.53  fof(f102,plain,(
% 1.34/0.53    spl5_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.34/0.53  fof(f785,plain,(
% 1.34/0.53    ~spl5_5 | spl5_8 | ~spl5_27),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f784])).
% 1.34/0.53  fof(f784,plain,(
% 1.34/0.53    $false | (~spl5_5 | spl5_8 | ~spl5_27)),
% 1.34/0.53    inference(global_subsumption,[],[f156,f774])).
% 1.34/0.53  fof(f156,plain,(
% 1.34/0.53    k1_xboole_0 != sK3 | spl5_8),
% 1.34/0.53    inference(avatar_component_clause,[],[f155])).
% 1.34/0.53  fof(f155,plain,(
% 1.34/0.53    spl5_8 <=> k1_xboole_0 = sK3),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.34/0.53  fof(f664,plain,(
% 1.34/0.53    ~spl5_3 | spl5_8 | ~spl5_28),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f663])).
% 1.34/0.53  fof(f663,plain,(
% 1.34/0.53    $false | (~spl5_3 | spl5_8 | ~spl5_28)),
% 1.34/0.53    inference(subsumption_resolution,[],[f662,f58])).
% 1.34/0.53  fof(f662,plain,(
% 1.34/0.53    ~r1_tarski(k1_xboole_0,sK3) | (~spl5_3 | spl5_8 | ~spl5_28)),
% 1.34/0.53    inference(subsumption_resolution,[],[f658,f156])).
% 1.34/0.53  fof(f658,plain,(
% 1.34/0.53    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | (~spl5_3 | ~spl5_28)),
% 1.34/0.53    inference(resolution,[],[f656,f71])).
% 1.34/0.53  fof(f71,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f46])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(flattening,[],[f45])).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(nnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.53  fof(f656,plain,(
% 1.34/0.53    r1_tarski(sK3,k1_xboole_0) | (~spl5_3 | ~spl5_28)),
% 1.34/0.53    inference(forward_demodulation,[],[f655,f90])).
% 1.34/0.53  fof(f90,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.34/0.53    inference(equality_resolution,[],[f76])).
% 1.34/0.53  fof(f76,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f49])).
% 1.34/0.53  fof(f655,plain,(
% 1.34/0.53    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl5_3 | ~spl5_28)),
% 1.34/0.53    inference(forward_demodulation,[],[f651,f532])).
% 1.34/0.53  fof(f532,plain,(
% 1.34/0.53    k1_xboole_0 = sK2 | ~spl5_28),
% 1.34/0.53    inference(avatar_component_clause,[],[f530])).
% 1.34/0.53  fof(f530,plain,(
% 1.34/0.53    spl5_28 <=> k1_xboole_0 = sK2),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.34/0.53  fof(f651,plain,(
% 1.34/0.53    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl5_3),
% 1.34/0.53    inference(resolution,[],[f107,f72])).
% 1.34/0.53  fof(f72,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f47])).
% 1.34/0.53  fof(f107,plain,(
% 1.34/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_3),
% 1.34/0.53    inference(avatar_component_clause,[],[f106])).
% 1.34/0.53  fof(f106,plain,(
% 1.34/0.53    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.34/0.53  fof(f642,plain,(
% 1.34/0.53    ~spl5_5 | spl5_26),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f641])).
% 1.34/0.53  fof(f641,plain,(
% 1.34/0.53    $false | (~spl5_5 | spl5_26)),
% 1.34/0.53    inference(subsumption_resolution,[],[f640,f58])).
% 1.34/0.53  fof(f640,plain,(
% 1.34/0.53    ~r1_tarski(k1_xboole_0,sK3) | (~spl5_5 | spl5_26)),
% 1.34/0.53    inference(forward_demodulation,[],[f613,f91])).
% 1.34/0.53  fof(f613,plain,(
% 1.34/0.53    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)),sK3) | (~spl5_5 | spl5_26)),
% 1.34/0.53    inference(superposition,[],[f479,f117])).
% 1.34/0.53  fof(f479,plain,(
% 1.34/0.53    ~r1_tarski(k2_zfmisc_1(sK0,k2_relat_1(sK3)),sK3) | spl5_26),
% 1.34/0.53    inference(avatar_component_clause,[],[f477])).
% 1.34/0.53  fof(f477,plain,(
% 1.34/0.53    spl5_26 <=> r1_tarski(k2_zfmisc_1(sK0,k2_relat_1(sK3)),sK3)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.34/0.53  fof(f547,plain,(
% 1.34/0.53    spl5_2 | spl5_4 | spl5_28),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f546])).
% 1.34/0.54  fof(f546,plain,(
% 1.34/0.54    $false | (spl5_2 | spl5_4 | spl5_28)),
% 1.34/0.54    inference(global_subsumption,[],[f528,f538,f531])).
% 1.34/0.54  fof(f531,plain,(
% 1.34/0.54    k1_xboole_0 != sK2 | spl5_28),
% 1.34/0.54    inference(avatar_component_clause,[],[f530])).
% 1.34/0.54  fof(f538,plain,(
% 1.34/0.54    sK0 = k1_relset_1(sK0,sK2,sK3) | spl5_4),
% 1.34/0.54    inference(forward_demodulation,[],[f522,f257])).
% 1.34/0.54  fof(f257,plain,(
% 1.34/0.54    sK0 = k1_relat_1(sK3) | spl5_4),
% 1.34/0.54    inference(superposition,[],[f203,f213])).
% 1.34/0.54  fof(f213,plain,(
% 1.34/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | spl5_4),
% 1.34/0.54    inference(subsumption_resolution,[],[f212,f113])).
% 1.34/0.54  fof(f113,plain,(
% 1.34/0.54    k1_xboole_0 != sK1 | spl5_4),
% 1.34/0.54    inference(avatar_component_clause,[],[f111])).
% 1.34/0.54  fof(f111,plain,(
% 1.34/0.54    spl5_4 <=> k1_xboole_0 = sK1),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.34/0.54  fof(f212,plain,(
% 1.34/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.34/0.54    inference(subsumption_resolution,[],[f208,f52])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    v1_funct_2(sK3,sK0,sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f41])).
% 1.34/0.54  fof(f41,plain,(
% 1.34/0.54    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.34/0.54    inference(flattening,[],[f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.34/0.54    inference(ennf_transformation,[],[f21])).
% 1.34/0.54  fof(f21,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.34/0.54    inference(negated_conjecture,[],[f20])).
% 1.34/0.54  fof(f20,conjecture,(
% 1.34/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.34/0.54  fof(f208,plain,(
% 1.34/0.54    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.34/0.54    inference(resolution,[],[f81,f53])).
% 1.34/0.54  fof(f53,plain,(
% 1.34/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.34/0.54    inference(cnf_transformation,[],[f41])).
% 1.34/0.54  fof(f81,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f50])).
% 1.34/0.54  fof(f203,plain,(
% 1.34/0.54    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.34/0.54    inference(resolution,[],[f79,f53])).
% 1.34/0.54  fof(f522,plain,(
% 1.34/0.54    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | spl5_4),
% 1.34/0.54    inference(resolution,[],[f516,f79])).
% 1.34/0.54  fof(f516,plain,(
% 1.34/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_4),
% 1.34/0.54    inference(resolution,[],[f350,f88])).
% 1.34/0.54  fof(f88,plain,(
% 1.34/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.54    inference(equality_resolution,[],[f70])).
% 1.34/0.54  fof(f70,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f46])).
% 1.34/0.54  fof(f350,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | spl5_4),
% 1.34/0.54    inference(forward_demodulation,[],[f349,f257])).
% 1.34/0.54  fof(f349,plain,(
% 1.34/0.54    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0)) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f346,f146])).
% 1.34/0.54  fof(f146,plain,(
% 1.34/0.54    v1_relat_1(sK3)),
% 1.34/0.54    inference(subsumption_resolution,[],[f144,f66])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,axiom,(
% 1.34/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.54  fof(f144,plain,(
% 1.34/0.54    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.34/0.54    inference(resolution,[],[f64,f53])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.54  fof(f346,plain,(
% 1.34/0.54    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 1.34/0.54    inference(resolution,[],[f256,f77])).
% 1.34/0.54  fof(f77,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.34/0.54    inference(flattening,[],[f32])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.34/0.54    inference(ennf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.34/0.54  fof(f256,plain,(
% 1.34/0.54    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.34/0.54    inference(superposition,[],[f54,f199])).
% 1.34/0.54  fof(f199,plain,(
% 1.34/0.54    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.34/0.54    inference(resolution,[],[f78,f53])).
% 1.34/0.54  fof(f78,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f41])).
% 1.34/0.54  fof(f528,plain,(
% 1.34/0.54    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | (spl5_2 | spl5_4)),
% 1.34/0.54    inference(subsumption_resolution,[],[f520,f104])).
% 1.34/0.54  fof(f520,plain,(
% 1.34/0.54    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | spl5_4),
% 1.34/0.54    inference(resolution,[],[f516,f83])).
% 1.34/0.54  fof(f83,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f50])).
% 1.34/0.54  fof(f518,plain,(
% 1.34/0.54    spl5_3 | spl5_4),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f517])).
% 1.34/0.54  fof(f517,plain,(
% 1.34/0.54    $false | (spl5_3 | spl5_4)),
% 1.34/0.54    inference(subsumption_resolution,[],[f516,f108])).
% 1.34/0.54  fof(f108,plain,(
% 1.34/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_3),
% 1.34/0.54    inference(avatar_component_clause,[],[f106])).
% 1.34/0.54  fof(f484,plain,(
% 1.34/0.54    ~spl5_26 | spl5_27),
% 1.34/0.54    inference(avatar_split_clause,[],[f474,f481,f477])).
% 1.34/0.54  fof(f474,plain,(
% 1.34/0.54    sK3 = k2_zfmisc_1(sK0,k2_relat_1(sK3)) | ~r1_tarski(k2_zfmisc_1(sK0,k2_relat_1(sK3)),sK3)),
% 1.34/0.54    inference(resolution,[],[f400,f71])).
% 1.34/0.54  fof(f400,plain,(
% 1.34/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,k2_relat_1(sK3)))),
% 1.34/0.54    inference(resolution,[],[f345,f72])).
% 1.34/0.54  fof(f345,plain,(
% 1.34/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK3))))),
% 1.34/0.54    inference(subsumption_resolution,[],[f343,f146])).
% 1.34/0.54  fof(f343,plain,(
% 1.34/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 1.34/0.54    inference(resolution,[],[f207,f196])).
% 1.34/0.54  fof(f196,plain,(
% 1.34/0.54    r1_tarski(k1_relat_1(sK3),sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f195,f146])).
% 1.34/0.54  fof(f195,plain,(
% 1.34/0.54    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 1.34/0.54    inference(resolution,[],[f181,f67])).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f44])).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.34/0.54  fof(f181,plain,(
% 1.34/0.54    v4_relat_1(sK3,sK0)),
% 1.34/0.54    inference(resolution,[],[f80,f53])).
% 1.34/0.54  fof(f80,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.34/0.54    inference(pure_predicate_removal,[],[f14])).
% 1.34/0.54  fof(f14,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.54  fof(f207,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(resolution,[],[f77,f88])).
% 1.34/0.54  fof(f464,plain,(
% 1.34/0.54    spl5_4 | spl5_5 | ~spl5_8),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f463])).
% 1.34/0.54  fof(f463,plain,(
% 1.34/0.54    $false | (spl5_4 | spl5_5 | ~spl5_8)),
% 1.34/0.54    inference(subsumption_resolution,[],[f462,f116])).
% 1.34/0.54  fof(f116,plain,(
% 1.34/0.54    k1_xboole_0 != sK0 | spl5_5),
% 1.34/0.54    inference(avatar_component_clause,[],[f115])).
% 1.34/0.54  fof(f462,plain,(
% 1.34/0.54    k1_xboole_0 = sK0 | (spl5_4 | ~spl5_8)),
% 1.34/0.54    inference(forward_demodulation,[],[f448,f260])).
% 1.34/0.54  fof(f448,plain,(
% 1.34/0.54    sK0 = k1_relat_1(k1_xboole_0) | (spl5_4 | ~spl5_8)),
% 1.34/0.54    inference(superposition,[],[f257,f157])).
% 1.34/0.54  fof(f157,plain,(
% 1.34/0.54    k1_xboole_0 = sK3 | ~spl5_8),
% 1.34/0.54    inference(avatar_component_clause,[],[f155])).
% 1.34/0.54  fof(f452,plain,(
% 1.34/0.54    spl5_3 | ~spl5_8),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f451])).
% 1.34/0.54  fof(f451,plain,(
% 1.34/0.54    $false | (spl5_3 | ~spl5_8)),
% 1.34/0.54    inference(subsumption_resolution,[],[f430,f142])).
% 1.34/0.54  fof(f430,plain,(
% 1.34/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl5_3 | ~spl5_8)),
% 1.34/0.54    inference(superposition,[],[f108,f157])).
% 1.34/0.54  fof(f132,plain,(
% 1.34/0.54    spl5_1),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f131])).
% 1.34/0.54  fof(f131,plain,(
% 1.34/0.54    $false | spl5_1),
% 1.34/0.54    inference(subsumption_resolution,[],[f100,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    v1_funct_1(sK3)),
% 1.34/0.54    inference(cnf_transformation,[],[f41])).
% 1.34/0.54  fof(f100,plain,(
% 1.34/0.54    ~v1_funct_1(sK3) | spl5_1),
% 1.34/0.54    inference(avatar_component_clause,[],[f98])).
% 1.34/0.54  fof(f98,plain,(
% 1.34/0.54    spl5_1 <=> v1_funct_1(sK3)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.34/0.54  fof(f118,plain,(
% 1.34/0.54    ~spl5_4 | spl5_5),
% 1.34/0.54    inference(avatar_split_clause,[],[f55,f115,f111])).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.34/0.54    inference(cnf_transformation,[],[f41])).
% 1.34/0.54  fof(f109,plain,(
% 1.34/0.54    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.34/0.54    inference(avatar_split_clause,[],[f56,f106,f102,f98])).
% 1.34/0.54  fof(f56,plain,(
% 1.34/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 1.34/0.54    inference(cnf_transformation,[],[f41])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (10732)------------------------------
% 1.34/0.54  % (10732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (10732)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (10732)Memory used [KB]: 11129
% 1.34/0.54  % (10732)Time elapsed: 0.081 s
% 1.34/0.54  % (10732)------------------------------
% 1.34/0.54  % (10732)------------------------------
% 1.34/0.54  % (10744)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.34/0.54  % (10737)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.34/0.54  % (10721)Success in time 0.173 s
%------------------------------------------------------------------------------
