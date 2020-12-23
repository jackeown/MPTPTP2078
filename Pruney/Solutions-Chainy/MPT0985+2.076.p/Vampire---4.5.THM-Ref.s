%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 994 expanded)
%              Number of leaves         :   26 ( 250 expanded)
%              Depth                    :   24
%              Number of atoms          :  536 (4743 expanded)
%              Number of equality atoms :  123 ( 932 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f799,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f128,f139,f142,f219,f380,f415,f528,f544,f553,f789,f798])).

fof(f798,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f796,f456])).

fof(f456,plain,(
    ! [X14] : v1_funct_2(k1_xboole_0,k1_xboole_0,X14) ),
    inference(subsumption_resolution,[],[f283,f453])).

fof(f453,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f251,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f77,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f251,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f250,f135])).

fof(f135,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f83,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f250,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f152,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f152,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f86,f61])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f283,plain,(
    ! [X14] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X14) ) ),
    inference(forward_demodulation,[],[f282,f187])).

fof(f187,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f282,plain,(
    ! [X14] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X14)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X14,k1_xboole_0) ) ),
    inference(resolution,[],[f133,f117])).

fof(f117,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f100,f96])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f100,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f133,plain,(
    ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f79,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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

fof(f796,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f795,f775])).

fof(f775,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f774,f60])).

fof(f774,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f773,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f773,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f772,f453])).

fof(f772,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f771,f555])).

fof(f555,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f554,f95])).

fof(f554,plain,
    ( sK2 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f543,f218])).

fof(f218,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f543,plain,
    ( sK2 = k2_zfmisc_1(k1_relat_1(sK2),sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl3_19
  <=> sK2 = k2_zfmisc_1(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f771,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f770,f95])).

fof(f770,plain,
    ( k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f769,f453])).

fof(f769,plain,
    ( k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f765,f555])).

fof(f765,plain,
    ( k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f530,f77])).

fof(f530,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f518,f302])).

fof(f302,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f301,f185])).

fof(f185,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f181,f58])).

fof(f58,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45])).

fof(f45,plain,
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

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f181,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f301,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f300,f134])).

fof(f134,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f56])).

fof(f300,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f179,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f179,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f518,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f493,f298])).

fof(f298,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f297,f134])).

fof(f297,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f180,f54])).

fof(f180,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f57])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f493,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))
    | ~ spl3_5 ),
    inference(resolution,[],[f175,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f175,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f171,f127])).

fof(f127,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f171,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f143,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f143,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f129,f134])).

fof(f129,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f54])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f795,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f794,f555])).

fof(f794,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f109,f218])).

fof(f109,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f789,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f788])).

fof(f788,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f785,f61])).

fof(f785,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(superposition,[],[f579,f775])).

fof(f579,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f578,f555])).

fof(f578,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f563,f96])).

fof(f563,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_11 ),
    inference(superposition,[],[f113,f218])).

fof(f113,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f553,plain,
    ( ~ spl3_11
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | ~ spl3_11
    | spl3_18 ),
    inference(subsumption_resolution,[],[f551,f60])).

fof(f551,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_11
    | spl3_18 ),
    inference(forward_demodulation,[],[f550,f95])).

fof(f550,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),sK2)
    | ~ spl3_11
    | spl3_18 ),
    inference(forward_demodulation,[],[f539,f218])).

fof(f539,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl3_18
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f544,plain,
    ( ~ spl3_18
    | spl3_19 ),
    inference(avatar_split_clause,[],[f424,f541,f537])).

fof(f424,plain,
    ( sK2 = k2_zfmisc_1(k1_relat_1(sK2),sK1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2) ),
    inference(resolution,[],[f271,f77])).

fof(f271,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK1)) ),
    inference(forward_demodulation,[],[f259,f185])).

fof(f259,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f170,f78])).

fof(f170,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f169,f134])).

fof(f169,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f54])).

fof(f528,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f526,f113])).

fof(f526,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f525,f302])).

fof(f525,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f495,f388])).

fof(f388,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl3_15
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f495,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_5 ),
    inference(superposition,[],[f175,f298])).

fof(f415,plain,
    ( ~ spl3_10
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl3_10
    | spl3_15 ),
    inference(global_subsumption,[],[f248,f387])).

fof(f387,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f386])).

fof(f248,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f186,f214])).

fof(f214,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl3_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f186,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f85,f56])).

fof(f380,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f378,f109])).

fof(f378,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f374,f302])).

fof(f374,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f176,f299])).

fof(f299,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f298,f248])).

fof(f176,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f172,f127])).

fof(f172,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f143,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f219,plain,
    ( spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f210,f216,f212])).

fof(f210,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f206,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f206,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f142,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f140,f134])).

fof(f140,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f129,f105])).

fof(f105,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f139,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f134,f123])).

fof(f123,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f128,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f67,f54])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f114,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f59,f111,f107,f103])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (12454)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (12462)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (12453)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (12459)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (12454)Refutation not found, incomplete strategy% (12454)------------------------------
% 0.20/0.51  % (12454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12470)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (12450)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (12451)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (12471)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (12455)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (12466)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (12461)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (12472)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (12469)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (12473)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (12465)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (12463)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (12450)Refutation not found, incomplete strategy% (12450)------------------------------
% 0.20/0.52  % (12450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12450)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12450)Memory used [KB]: 10874
% 0.20/0.52  % (12450)Time elapsed: 0.108 s
% 0.20/0.52  % (12450)------------------------------
% 0.20/0.52  % (12450)------------------------------
% 0.20/0.53  % (12454)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12454)Memory used [KB]: 6396
% 0.20/0.53  % (12454)Time elapsed: 0.102 s
% 0.20/0.53  % (12454)------------------------------
% 0.20/0.53  % (12454)------------------------------
% 0.20/0.53  % (12456)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (12460)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (12452)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (12464)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (12449)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (12457)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (12455)Refutation not found, incomplete strategy% (12455)------------------------------
% 0.20/0.54  % (12455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12455)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12455)Memory used [KB]: 10618
% 0.20/0.54  % (12455)Time elapsed: 0.106 s
% 0.20/0.54  % (12455)------------------------------
% 0.20/0.54  % (12455)------------------------------
% 0.20/0.54  % (12459)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f799,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f114,f128,f139,f142,f219,f380,f415,f528,f544,f553,f789,f798])).
% 0.20/0.54  fof(f798,plain,(
% 0.20/0.54    spl3_2 | ~spl3_5 | ~spl3_11 | ~spl3_19),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f797])).
% 0.20/0.54  fof(f797,plain,(
% 0.20/0.54    $false | (spl3_2 | ~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(subsumption_resolution,[],[f796,f456])).
% 0.20/0.54  fof(f456,plain,(
% 0.20/0.54    ( ! [X14] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X14)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f283,f453])).
% 0.20/0.54  fof(f453,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.54    inference(resolution,[],[f251,f147])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f77,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f251,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f250,f135])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    v1_relat_1(k1_xboole_0)),
% 0.20/0.54    inference(resolution,[],[f83,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.54  fof(f250,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.54    inference(resolution,[],[f152,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f86,f61])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.54  fof(f283,plain,(
% 0.20/0.54    ( ! [X14] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X14)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f282,f187])).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 0.20/0.54    inference(resolution,[],[f85,f61])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.54  fof(f282,plain,(
% 0.20/0.54    ( ! [X14] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X14) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X14,k1_xboole_0)) )),
% 0.20/0.54    inference(resolution,[],[f133,f117])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f100,f96])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(flattening,[],[f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.54    inference(equality_resolution,[],[f90])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(resolution,[],[f79,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f49])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f796,plain,(
% 0.20/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl3_2 | ~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f795,f775])).
% 0.20/0.54  fof(f775,plain,(
% 0.20/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(subsumption_resolution,[],[f774,f60])).
% 0.20/0.54  fof(f774,plain,(
% 0.20/0.54    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f773,f95])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f773,plain,(
% 0.20/0.54    ~r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f772,f453])).
% 0.20/0.54  fof(f772,plain,(
% 0.20/0.54    ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f771,f555])).
% 0.20/0.54  fof(f555,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | (~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f554,f95])).
% 0.20/0.54  fof(f554,plain,(
% 0.20/0.54    sK2 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) | (~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f543,f218])).
% 0.20/0.54  fof(f218,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | ~spl3_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f216])).
% 0.20/0.54  fof(f216,plain,(
% 0.20/0.54    spl3_11 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.54  fof(f543,plain,(
% 0.20/0.54    sK2 = k2_zfmisc_1(k1_relat_1(sK2),sK1) | ~spl3_19),
% 0.20/0.54    inference(avatar_component_clause,[],[f541])).
% 0.20/0.54  fof(f541,plain,(
% 0.20/0.54    spl3_19 <=> sK2 = k2_zfmisc_1(k1_relat_1(sK2),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.54  fof(f771,plain,(
% 0.20/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f770,f95])).
% 0.20/0.54  fof(f770,plain,(
% 0.20/0.54    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f769,f453])).
% 0.20/0.54  fof(f769,plain,(
% 0.20/0.54    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)) | ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f765,f555])).
% 0.20/0.54  fof(f765,plain,(
% 0.20/0.54    k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) | ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | ~spl3_5),
% 0.20/0.54    inference(resolution,[],[f530,f77])).
% 0.20/0.54  fof(f530,plain,(
% 0.20/0.54    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) | ~spl3_5),
% 0.20/0.54    inference(forward_demodulation,[],[f518,f302])).
% 0.20/0.54  fof(f302,plain,(
% 0.20/0.54    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(forward_demodulation,[],[f301,f185])).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    sK1 = k2_relat_1(sK2)),
% 0.20/0.54    inference(forward_demodulation,[],[f181,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f20])).
% 0.20/0.54  fof(f20,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.54  fof(f181,plain,(
% 0.20/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f84,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f300,f134])).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f83,f56])).
% 0.20/0.54  fof(f300,plain,(
% 0.20/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f179,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    v1_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f69,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    v2_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.54  fof(f518,plain,(
% 0.20/0.54    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))) | ~spl3_5),
% 0.20/0.54    inference(forward_demodulation,[],[f493,f298])).
% 0.20/0.54  fof(f298,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f297,f134])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f180,f54])).
% 0.20/0.54  fof(f180,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f70,f57])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f493,plain,(
% 0.20/0.54    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))) | ~spl3_5),
% 0.20/0.54    inference(resolution,[],[f175,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f50])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_5),
% 0.20/0.54    inference(subsumption_resolution,[],[f171,f127])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f125])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    spl3_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f143,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f129,f134])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f68,f54])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.54  fof(f795,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f794,f555])).
% 0.20/0.54  fof(f794,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_11)),
% 0.20/0.54    inference(forward_demodulation,[],[f109,f218])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f107])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.54  fof(f789,plain,(
% 0.20/0.54    spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_19),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f788])).
% 0.20/0.54  fof(f788,plain,(
% 0.20/0.54    $false | (spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(subsumption_resolution,[],[f785,f61])).
% 0.20/0.54  fof(f785,plain,(
% 0.20/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(superposition,[],[f579,f775])).
% 0.20/0.54  fof(f579,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl3_3 | ~spl3_11 | ~spl3_19)),
% 0.20/0.54    inference(forward_demodulation,[],[f578,f555])).
% 0.20/0.54  fof(f578,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_3 | ~spl3_11)),
% 0.20/0.54    inference(forward_demodulation,[],[f563,f96])).
% 0.20/0.54  fof(f563,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_11)),
% 0.20/0.54    inference(superposition,[],[f113,f218])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f111])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.54  fof(f553,plain,(
% 0.20/0.54    ~spl3_11 | spl3_18),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f552])).
% 0.20/0.54  fof(f552,plain,(
% 0.20/0.54    $false | (~spl3_11 | spl3_18)),
% 0.20/0.54    inference(subsumption_resolution,[],[f551,f60])).
% 0.20/0.54  fof(f551,plain,(
% 0.20/0.54    ~r1_tarski(k1_xboole_0,sK2) | (~spl3_11 | spl3_18)),
% 0.20/0.54    inference(forward_demodulation,[],[f550,f95])).
% 0.20/0.54  fof(f550,plain,(
% 0.20/0.54    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),sK2) | (~spl3_11 | spl3_18)),
% 0.20/0.54    inference(forward_demodulation,[],[f539,f218])).
% 0.20/0.54  fof(f539,plain,(
% 0.20/0.54    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2) | spl3_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f537])).
% 0.20/0.54  fof(f537,plain,(
% 0.20/0.54    spl3_18 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.54  fof(f544,plain,(
% 0.20/0.54    ~spl3_18 | spl3_19),
% 0.20/0.54    inference(avatar_split_clause,[],[f424,f541,f537])).
% 0.20/0.54  fof(f424,plain,(
% 0.20/0.54    sK2 = k2_zfmisc_1(k1_relat_1(sK2),sK1) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2)),
% 0.20/0.54    inference(resolution,[],[f271,f77])).
% 0.20/0.54  fof(f271,plain,(
% 0.20/0.54    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f259,f185])).
% 0.20/0.54  fof(f259,plain,(
% 0.20/0.54    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.54    inference(resolution,[],[f170,f78])).
% 0.20/0.54  fof(f170,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.54    inference(subsumption_resolution,[],[f169,f134])).
% 0.20/0.54  fof(f169,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f66,f54])).
% 0.20/0.54  fof(f528,plain,(
% 0.20/0.54    spl3_3 | ~spl3_5 | ~spl3_15),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f527])).
% 0.20/0.54  fof(f527,plain,(
% 0.20/0.54    $false | (spl3_3 | ~spl3_5 | ~spl3_15)),
% 0.20/0.54    inference(subsumption_resolution,[],[f526,f113])).
% 0.20/0.54  fof(f526,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_5 | ~spl3_15)),
% 0.20/0.54    inference(forward_demodulation,[],[f525,f302])).
% 0.20/0.54  fof(f525,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl3_5 | ~spl3_15)),
% 0.20/0.54    inference(forward_demodulation,[],[f495,f388])).
% 0.20/0.54  fof(f388,plain,(
% 0.20/0.54    sK0 = k1_relat_1(sK2) | ~spl3_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f386])).
% 0.20/0.54  fof(f386,plain,(
% 0.20/0.54    spl3_15 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.54  fof(f495,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~spl3_5),
% 0.20/0.54    inference(superposition,[],[f175,f298])).
% 0.20/0.54  fof(f415,plain,(
% 0.20/0.54    ~spl3_10 | spl3_15),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f414])).
% 0.20/0.54  fof(f414,plain,(
% 0.20/0.54    $false | (~spl3_10 | spl3_15)),
% 0.20/0.54    inference(global_subsumption,[],[f248,f387])).
% 0.20/0.54  fof(f387,plain,(
% 0.20/0.54    sK0 != k1_relat_1(sK2) | spl3_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f386])).
% 0.20/0.54  fof(f248,plain,(
% 0.20/0.54    sK0 = k1_relat_1(sK2) | ~spl3_10),
% 0.20/0.54    inference(superposition,[],[f186,f214])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f212])).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    spl3_10 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.54  fof(f186,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.54    inference(resolution,[],[f85,f56])).
% 0.20/0.54  fof(f380,plain,(
% 0.20/0.54    spl3_2 | ~spl3_5 | ~spl3_10),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f379])).
% 0.20/0.54  fof(f379,plain,(
% 0.20/0.54    $false | (spl3_2 | ~spl3_5 | ~spl3_10)),
% 0.20/0.54    inference(subsumption_resolution,[],[f378,f109])).
% 0.20/0.54  fof(f378,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_5 | ~spl3_10)),
% 0.20/0.54    inference(forward_demodulation,[],[f374,f302])).
% 0.20/0.54  fof(f374,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl3_5 | ~spl3_10)),
% 0.20/0.54    inference(superposition,[],[f176,f299])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl3_10),
% 0.20/0.54    inference(forward_demodulation,[],[f298,f248])).
% 0.20/0.54  fof(f176,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_5),
% 0.20/0.54    inference(subsumption_resolution,[],[f172,f127])).
% 0.20/0.54  fof(f172,plain,(
% 0.20/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f143,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    spl3_10 | spl3_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f210,f216,f212])).
% 0.20/0.54  fof(f210,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f206,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f206,plain,(
% 0.20/0.54    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.54    inference(resolution,[],[f87,f56])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f53])).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    spl3_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    $false | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f140,f134])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f129,f105])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f103])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    spl3_4),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    $false | spl3_4),
% 0.20/0.54    inference(subsumption_resolution,[],[f134,f123])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | spl3_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f121])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    spl3_4 <=> v1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    ~spl3_4 | spl3_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f119,f125,f121])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f67,f54])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f59,f111,f107,f103])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (12459)------------------------------
% 0.20/0.54  % (12459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12459)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (12459)Memory used [KB]: 11001
% 0.20/0.54  % (12459)Time elapsed: 0.127 s
% 0.20/0.54  % (12459)------------------------------
% 0.20/0.54  % (12459)------------------------------
% 0.20/0.54  % (12448)Success in time 0.177 s
%------------------------------------------------------------------------------
