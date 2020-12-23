%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:18 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 816 expanded)
%              Number of leaves         :   18 ( 203 expanded)
%              Depth                    :   17
%              Number of atoms          :  489 (4298 expanded)
%              Number of equality atoms :  126 ( 969 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f619,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f116,f124,f127,f181,f278,f362,f399,f528,f618])).

fof(f618,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f570,f614])).

fof(f614,plain,
    ( ! [X0] : v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f571,f574])).

fof(f574,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f418,f540])).

fof(f540,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f539,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f539,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f200,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f200,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_11
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f418,plain,
    ( ! [X2] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f417,f180])).

fof(f417,plain,
    ( ! [X2] : sK1 = k1_relset_1(k1_xboole_0,X2,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f416,f149])).

fof(f149,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f146,f43])).

fof(f43,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31])).

fof(f31,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f146,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f65,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f416,plain,
    ( ! [X2] : k2_relat_1(sK2) = k1_relset_1(k1_xboole_0,X2,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f407,f138])).

fof(f138,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f137,f120])).

fof(f120,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f41])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f137,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f39])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f136,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f42])).

fof(f42,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f407,plain,
    ( ! [X2] : k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k1_xboole_0,X2,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f402,f145])).

fof(f145,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f64,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f402,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f401,f76])).

fof(f401,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f92,f180])).

fof(f92,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f571,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0))
        | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0) )
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f404,f540])).

fof(f404,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2))
        | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f402,f105])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f80,f76])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f570,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f403,f540])).

fof(f403,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f89,f180])).

fof(f89,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f528,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | spl3_11 ),
    inference(subsumption_resolution,[],[f517,f501])).

fof(f501,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f500])).

fof(f500,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(superposition,[],[f404,f415])).

fof(f415,plain,
    ( ! [X1] : k1_xboole_0 = k1_relset_1(X1,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f414,f180])).

fof(f414,plain,
    ( ! [X1] : sK1 = k1_relset_1(X1,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f413,f149])).

fof(f413,plain,
    ( ! [X1] : k2_relat_1(sK2) = k1_relset_1(X1,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f406,f138])).

fof(f406,plain,
    ( ! [X1] : k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(X1,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f402,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_relat_1(X1) = k1_relset_1(X0,k1_xboole_0,X1) ) ),
    inference(superposition,[],[f64,f75])).

fof(f517,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_9
    | spl3_11 ),
    inference(superposition,[],[f403,f458])).

fof(f458,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_9
    | spl3_11 ),
    inference(subsumption_resolution,[],[f457,f436])).

fof(f436,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f424,f75])).

fof(f424,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_9 ),
    inference(superposition,[],[f41,f180])).

fof(f457,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | ~ spl3_9
    | spl3_11 ),
    inference(subsumption_resolution,[],[f456,f440])).

fof(f440,plain,
    ( k1_xboole_0 != sK2
    | ~ spl3_9
    | spl3_11 ),
    inference(forward_demodulation,[],[f431,f75])).

fof(f431,plain,
    ( sK2 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl3_9
    | spl3_11 ),
    inference(superposition,[],[f199,f180])).

fof(f199,plain,
    ( sK2 != k2_zfmisc_1(sK0,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f198])).

fof(f456,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(resolution,[],[f423,f104])).

fof(f104,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f79,f75])).

fof(f79,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f423,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(superposition,[],[f40,f180])).

fof(f40,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f399,plain,
    ( spl3_3
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl3_3
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f390,f93])).

fof(f93,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f390,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f161,f386])).

fof(f386,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f176,f143])).

fof(f143,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f64,f41])).

fof(f176,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f161,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f160,f149])).

fof(f160,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f159,f138])).

fof(f159,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f158,f141])).

fof(f141,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f140,f120])).

fof(f140,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f139,f39])).

fof(f139,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f42])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f158,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f154,f115])).

fof(f115,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f154,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f128,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f128,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f117,f120])).

fof(f117,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f362,plain,
    ( spl3_3
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | spl3_3
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f360,f294])).

fof(f294,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f286,f76])).

fof(f286,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_9 ),
    inference(superposition,[],[f93,f180])).

fof(f360,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f349,f76])).

fof(f349,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f161,f180])).

fof(f278,plain,
    ( spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f276,f89])).

fof(f276,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f165,f221])).

fof(f221,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f143,f176])).

fof(f165,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f164,f149])).

fof(f164,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f163,f138])).

fof(f163,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f162,f141])).

fof(f162,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f155,f115])).

fof(f155,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f128,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f181,plain,
    ( spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f172,f178,f174])).

fof(f172,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f169,f40])).

fof(f169,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f67,f41])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f127,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f125,f120])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f117,f85])).

fof(f85,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f124,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f120,f111])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f116,plain,
    ( ~ spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f107,f113,f109])).

fof(f107,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f39])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f94,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f91,f87,f83])).

fof(f44,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (14932)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (14948)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (14925)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (14930)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (14926)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (14934)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (14933)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (14946)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (14936)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (14935)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (14938)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (14942)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (14939)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (14927)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (14947)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (14926)Refutation not found, incomplete strategy% (14926)------------------------------
% 0.21/0.52  % (14926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14926)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14926)Memory used [KB]: 10746
% 0.21/0.52  % (14926)Time elapsed: 0.097 s
% 0.21/0.52  % (14926)------------------------------
% 0.21/0.52  % (14926)------------------------------
% 0.21/0.52  % (14929)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (14931)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (14928)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (14949)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (14931)Refutation not found, incomplete strategy% (14931)------------------------------
% 0.21/0.53  % (14931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14931)Memory used [KB]: 10618
% 0.21/0.53  % (14931)Time elapsed: 0.084 s
% 0.21/0.53  % (14931)------------------------------
% 0.21/0.53  % (14931)------------------------------
% 0.21/0.53  % (14945)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (14937)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (14940)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (14943)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.44/0.54  % (14935)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % SZS output start Proof for theBenchmark
% 1.44/0.54  fof(f619,plain,(
% 1.44/0.54    $false),
% 1.44/0.54    inference(avatar_sat_refutation,[],[f94,f116,f124,f127,f181,f278,f362,f399,f528,f618])).
% 1.44/0.54  fof(f618,plain,(
% 1.44/0.54    spl3_2 | ~spl3_3 | ~spl3_9 | ~spl3_11),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f617])).
% 1.44/0.54  fof(f617,plain,(
% 1.44/0.54    $false | (spl3_2 | ~spl3_3 | ~spl3_9 | ~spl3_11)),
% 1.44/0.54    inference(subsumption_resolution,[],[f570,f614])).
% 1.44/0.54  fof(f614,plain,(
% 1.44/0.54    ( ! [X0] : (v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)) ) | (~spl3_3 | ~spl3_9 | ~spl3_11)),
% 1.44/0.54    inference(subsumption_resolution,[],[f571,f574])).
% 1.44/0.54  fof(f574,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0))) ) | (~spl3_3 | ~spl3_9 | ~spl3_11)),
% 1.44/0.54    inference(superposition,[],[f418,f540])).
% 1.44/0.54  fof(f540,plain,(
% 1.44/0.54    k1_xboole_0 = sK2 | (~spl3_9 | ~spl3_11)),
% 1.44/0.54    inference(forward_demodulation,[],[f539,f75])).
% 1.44/0.54  fof(f75,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.44/0.54    inference(equality_resolution,[],[f62])).
% 1.44/0.54  fof(f62,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.44/0.54    inference(cnf_transformation,[],[f37])).
% 1.44/0.54  fof(f37,plain,(
% 1.44/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.44/0.54    inference(flattening,[],[f36])).
% 1.44/0.54  fof(f36,plain,(
% 1.44/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.44/0.54    inference(nnf_transformation,[],[f2])).
% 1.44/0.54  fof(f2,axiom,(
% 1.44/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.44/0.54  fof(f539,plain,(
% 1.44/0.54    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl3_9 | ~spl3_11)),
% 1.44/0.54    inference(forward_demodulation,[],[f200,f180])).
% 1.44/0.54  fof(f180,plain,(
% 1.44/0.54    k1_xboole_0 = sK1 | ~spl3_9),
% 1.44/0.54    inference(avatar_component_clause,[],[f178])).
% 1.44/0.54  fof(f178,plain,(
% 1.44/0.54    spl3_9 <=> k1_xboole_0 = sK1),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.44/0.54  fof(f200,plain,(
% 1.44/0.54    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl3_11),
% 1.44/0.54    inference(avatar_component_clause,[],[f198])).
% 1.44/0.54  fof(f198,plain,(
% 1.44/0.54    spl3_11 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.44/0.54  fof(f418,plain,(
% 1.44/0.54    ( ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k2_funct_1(sK2))) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f417,f180])).
% 1.44/0.54  fof(f417,plain,(
% 1.44/0.54    ( ! [X2] : (sK1 = k1_relset_1(k1_xboole_0,X2,k2_funct_1(sK2))) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f416,f149])).
% 1.44/0.54  fof(f149,plain,(
% 1.44/0.54    sK1 = k2_relat_1(sK2)),
% 1.44/0.54    inference(forward_demodulation,[],[f146,f43])).
% 1.44/0.54  fof(f43,plain,(
% 1.44/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  fof(f32,plain,(
% 1.44/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31])).
% 1.44/0.54  fof(f31,plain,(
% 1.44/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f16,plain,(
% 1.44/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.44/0.54    inference(flattening,[],[f15])).
% 1.44/0.54  fof(f15,plain,(
% 1.44/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.44/0.54    inference(ennf_transformation,[],[f14])).
% 1.44/0.54  fof(f14,negated_conjecture,(
% 1.44/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.44/0.54    inference(negated_conjecture,[],[f13])).
% 1.44/0.54  fof(f13,conjecture,(
% 1.44/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.44/0.54  fof(f146,plain,(
% 1.44/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f65,f41])).
% 1.44/0.54  fof(f41,plain,(
% 1.44/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  fof(f65,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f27])).
% 1.44/0.54  fof(f27,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f9])).
% 1.44/0.54  fof(f9,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.44/0.54  fof(f416,plain,(
% 1.44/0.54    ( ! [X2] : (k2_relat_1(sK2) = k1_relset_1(k1_xboole_0,X2,k2_funct_1(sK2))) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f407,f138])).
% 1.44/0.54  fof(f138,plain,(
% 1.44/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.44/0.54    inference(subsumption_resolution,[],[f137,f120])).
% 1.44/0.54  fof(f120,plain,(
% 1.44/0.54    v1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f63,f41])).
% 1.44/0.54  fof(f63,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f25,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f6])).
% 1.44/0.54  fof(f6,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.44/0.54  fof(f137,plain,(
% 1.44/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.44/0.54    inference(subsumption_resolution,[],[f136,f39])).
% 1.44/0.54  fof(f39,plain,(
% 1.44/0.54    v1_funct_1(sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  fof(f136,plain,(
% 1.44/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f50,f42])).
% 1.44/0.54  fof(f42,plain,(
% 1.44/0.54    v2_funct_1(sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  fof(f50,plain,(
% 1.44/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f22])).
% 1.44/0.54  fof(f22,plain,(
% 1.44/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(flattening,[],[f21])).
% 1.44/0.54  fof(f21,plain,(
% 1.44/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f5])).
% 1.44/0.54  fof(f5,axiom,(
% 1.44/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.44/0.54  fof(f407,plain,(
% 1.44/0.54    ( ! [X2] : (k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k1_xboole_0,X2,k2_funct_1(sK2))) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(resolution,[],[f402,f145])).
% 1.44/0.54  fof(f145,plain,(
% 1.44/0.54    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 1.44/0.54    inference(superposition,[],[f64,f76])).
% 1.44/0.54  fof(f76,plain,(
% 1.44/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.44/0.54    inference(equality_resolution,[],[f61])).
% 1.44/0.54  fof(f61,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.44/0.54    inference(cnf_transformation,[],[f37])).
% 1.44/0.54  fof(f64,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f26])).
% 1.44/0.54  fof(f26,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f8])).
% 1.44/0.54  fof(f8,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.44/0.54  fof(f402,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f401,f76])).
% 1.44/0.54  fof(f401,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f92,f180])).
% 1.44/0.54  fof(f92,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_3),
% 1.44/0.54    inference(avatar_component_clause,[],[f91])).
% 1.44/0.54  fof(f91,plain,(
% 1.44/0.54    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.44/0.54  fof(f571,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)) ) | (~spl3_3 | ~spl3_9 | ~spl3_11)),
% 1.44/0.54    inference(superposition,[],[f404,f540])).
% 1.44/0.54  fof(f404,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(resolution,[],[f402,f105])).
% 1.44/0.54  fof(f105,plain,(
% 1.44/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.44/0.54    inference(forward_demodulation,[],[f80,f76])).
% 1.44/0.54  fof(f80,plain,(
% 1.44/0.54    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.44/0.54    inference(equality_resolution,[],[f70])).
% 1.44/0.54  fof(f70,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f38])).
% 1.44/0.54  fof(f38,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(nnf_transformation,[],[f30])).
% 1.44/0.54  fof(f30,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(flattening,[],[f29])).
% 1.44/0.54  fof(f29,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f10])).
% 1.44/0.54  fof(f10,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.44/0.54  fof(f570,plain,(
% 1.44/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_9 | ~spl3_11)),
% 1.44/0.54    inference(superposition,[],[f403,f540])).
% 1.44/0.54  fof(f403,plain,(
% 1.44/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f89,f180])).
% 1.44/0.54  fof(f89,plain,(
% 1.44/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 1.44/0.54    inference(avatar_component_clause,[],[f87])).
% 1.44/0.54  fof(f87,plain,(
% 1.44/0.54    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.54  fof(f528,plain,(
% 1.44/0.54    spl3_2 | ~spl3_3 | ~spl3_9 | spl3_11),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f527])).
% 1.44/0.54  fof(f527,plain,(
% 1.44/0.54    $false | (spl3_2 | ~spl3_3 | ~spl3_9 | spl3_11)),
% 1.44/0.54    inference(subsumption_resolution,[],[f517,f501])).
% 1.44/0.54  fof(f501,plain,(
% 1.44/0.54    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(trivial_inequality_removal,[],[f500])).
% 1.44/0.54  fof(f500,plain,(
% 1.44/0.54    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(superposition,[],[f404,f415])).
% 1.44/0.54  fof(f415,plain,(
% 1.44/0.54    ( ! [X1] : (k1_xboole_0 = k1_relset_1(X1,k1_xboole_0,k2_funct_1(sK2))) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f414,f180])).
% 1.44/0.54  fof(f414,plain,(
% 1.44/0.54    ( ! [X1] : (sK1 = k1_relset_1(X1,k1_xboole_0,k2_funct_1(sK2))) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f413,f149])).
% 1.44/0.54  fof(f413,plain,(
% 1.44/0.54    ( ! [X1] : (k2_relat_1(sK2) = k1_relset_1(X1,k1_xboole_0,k2_funct_1(sK2))) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f406,f138])).
% 1.44/0.54  fof(f406,plain,(
% 1.44/0.54    ( ! [X1] : (k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(X1,k1_xboole_0,k2_funct_1(sK2))) ) | (~spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(resolution,[],[f402,f144])).
% 1.44/0.54  fof(f144,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_relat_1(X1) = k1_relset_1(X0,k1_xboole_0,X1)) )),
% 1.44/0.54    inference(superposition,[],[f64,f75])).
% 1.44/0.54  fof(f517,plain,(
% 1.44/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_9 | spl3_11)),
% 1.44/0.54    inference(superposition,[],[f403,f458])).
% 1.44/0.54  fof(f458,plain,(
% 1.44/0.54    k1_xboole_0 = sK0 | (~spl3_9 | spl3_11)),
% 1.44/0.54    inference(subsumption_resolution,[],[f457,f436])).
% 1.44/0.54  fof(f436,plain,(
% 1.44/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_9),
% 1.44/0.54    inference(forward_demodulation,[],[f424,f75])).
% 1.44/0.54  fof(f424,plain,(
% 1.44/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_9),
% 1.44/0.54    inference(superposition,[],[f41,f180])).
% 1.44/0.54  fof(f457,plain,(
% 1.44/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | (~spl3_9 | spl3_11)),
% 1.44/0.54    inference(subsumption_resolution,[],[f456,f440])).
% 1.44/0.54  fof(f440,plain,(
% 1.44/0.54    k1_xboole_0 != sK2 | (~spl3_9 | spl3_11)),
% 1.44/0.54    inference(forward_demodulation,[],[f431,f75])).
% 1.44/0.54  fof(f431,plain,(
% 1.44/0.54    sK2 != k2_zfmisc_1(sK0,k1_xboole_0) | (~spl3_9 | spl3_11)),
% 1.44/0.54    inference(superposition,[],[f199,f180])).
% 1.44/0.54  fof(f199,plain,(
% 1.44/0.54    sK2 != k2_zfmisc_1(sK0,sK1) | spl3_11),
% 1.44/0.54    inference(avatar_component_clause,[],[f198])).
% 1.44/0.54  fof(f456,plain,(
% 1.44/0.54    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | ~spl3_9),
% 1.44/0.54    inference(resolution,[],[f423,f104])).
% 1.44/0.54  fof(f104,plain,(
% 1.44/0.54    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 1.44/0.54    inference(forward_demodulation,[],[f79,f75])).
% 1.44/0.54  fof(f79,plain,(
% 1.44/0.54    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.44/0.54    inference(equality_resolution,[],[f71])).
% 1.44/0.54  fof(f71,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f38])).
% 1.44/0.54  fof(f423,plain,(
% 1.44/0.54    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl3_9),
% 1.44/0.54    inference(superposition,[],[f40,f180])).
% 1.44/0.54  fof(f40,plain,(
% 1.44/0.54    v1_funct_2(sK2,sK0,sK1)),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  fof(f399,plain,(
% 1.44/0.54    spl3_3 | ~spl3_7 | ~spl3_8),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f398])).
% 1.44/0.54  fof(f398,plain,(
% 1.44/0.54    $false | (spl3_3 | ~spl3_7 | ~spl3_8)),
% 1.44/0.54    inference(subsumption_resolution,[],[f390,f93])).
% 1.44/0.54  fof(f93,plain,(
% 1.44/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 1.44/0.54    inference(avatar_component_clause,[],[f91])).
% 1.44/0.54  fof(f390,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_7 | ~spl3_8)),
% 1.44/0.54    inference(superposition,[],[f161,f386])).
% 1.44/0.54  fof(f386,plain,(
% 1.44/0.54    sK0 = k1_relat_1(sK2) | ~spl3_8),
% 1.44/0.54    inference(superposition,[],[f176,f143])).
% 1.44/0.54  fof(f143,plain,(
% 1.44/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.44/0.54    inference(resolution,[],[f64,f41])).
% 1.44/0.54  fof(f176,plain,(
% 1.44/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_8),
% 1.44/0.54    inference(avatar_component_clause,[],[f174])).
% 1.44/0.54  fof(f174,plain,(
% 1.44/0.54    spl3_8 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.44/0.54  fof(f161,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl3_7),
% 1.44/0.54    inference(forward_demodulation,[],[f160,f149])).
% 1.44/0.54  fof(f160,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_7),
% 1.44/0.54    inference(forward_demodulation,[],[f159,f138])).
% 1.44/0.54  fof(f159,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~spl3_7),
% 1.44/0.54    inference(forward_demodulation,[],[f158,f141])).
% 1.44/0.54  fof(f141,plain,(
% 1.44/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.44/0.54    inference(subsumption_resolution,[],[f140,f120])).
% 1.44/0.54  fof(f140,plain,(
% 1.44/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.44/0.54    inference(subsumption_resolution,[],[f139,f39])).
% 1.44/0.54  fof(f139,plain,(
% 1.44/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f51,f42])).
% 1.44/0.54  fof(f51,plain,(
% 1.44/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f22])).
% 1.44/0.54  fof(f158,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_7),
% 1.44/0.54    inference(subsumption_resolution,[],[f154,f115])).
% 1.44/0.54  fof(f115,plain,(
% 1.44/0.54    v1_relat_1(k2_funct_1(sK2)) | ~spl3_7),
% 1.44/0.54    inference(avatar_component_clause,[],[f113])).
% 1.44/0.54  fof(f113,plain,(
% 1.44/0.54    spl3_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.44/0.54  fof(f154,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.44/0.54    inference(resolution,[],[f128,f47])).
% 1.44/0.54  fof(f47,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f18])).
% 1.44/0.54  fof(f18,plain,(
% 1.44/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(flattening,[],[f17])).
% 1.44/0.54  fof(f17,plain,(
% 1.44/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f11])).
% 1.44/0.54  fof(f11,axiom,(
% 1.44/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.44/0.54  fof(f128,plain,(
% 1.44/0.54    v1_funct_1(k2_funct_1(sK2))),
% 1.44/0.54    inference(subsumption_resolution,[],[f117,f120])).
% 1.44/0.54  fof(f117,plain,(
% 1.44/0.54    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f49,f39])).
% 1.44/0.54  fof(f49,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f20])).
% 1.44/0.54  fof(f20,plain,(
% 1.44/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(flattening,[],[f19])).
% 1.44/0.54  fof(f19,plain,(
% 1.44/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f4])).
% 1.44/0.54  fof(f4,axiom,(
% 1.44/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.44/0.54  fof(f362,plain,(
% 1.44/0.54    spl3_3 | ~spl3_7 | ~spl3_9),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f361])).
% 1.44/0.54  fof(f361,plain,(
% 1.44/0.54    $false | (spl3_3 | ~spl3_7 | ~spl3_9)),
% 1.44/0.54    inference(subsumption_resolution,[],[f360,f294])).
% 1.44/0.54  fof(f294,plain,(
% 1.44/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f286,f76])).
% 1.44/0.54  fof(f286,plain,(
% 1.44/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_9)),
% 1.44/0.54    inference(superposition,[],[f93,f180])).
% 1.44/0.54  fof(f360,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl3_7 | ~spl3_9)),
% 1.44/0.54    inference(forward_demodulation,[],[f349,f76])).
% 1.44/0.54  fof(f349,plain,(
% 1.44/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl3_7 | ~spl3_9)),
% 1.44/0.54    inference(superposition,[],[f161,f180])).
% 1.44/0.54  fof(f278,plain,(
% 1.44/0.54    spl3_2 | ~spl3_7 | ~spl3_8),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f277])).
% 1.44/0.54  fof(f277,plain,(
% 1.44/0.54    $false | (spl3_2 | ~spl3_7 | ~spl3_8)),
% 1.44/0.54    inference(subsumption_resolution,[],[f276,f89])).
% 1.44/0.54  fof(f276,plain,(
% 1.44/0.54    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_7 | ~spl3_8)),
% 1.44/0.54    inference(superposition,[],[f165,f221])).
% 1.44/0.54  fof(f221,plain,(
% 1.44/0.54    sK0 = k1_relat_1(sK2) | ~spl3_8),
% 1.44/0.54    inference(superposition,[],[f143,f176])).
% 1.44/0.54  fof(f165,plain,(
% 1.44/0.54    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~spl3_7),
% 1.44/0.54    inference(forward_demodulation,[],[f164,f149])).
% 1.44/0.54  fof(f164,plain,(
% 1.44/0.54    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_7),
% 1.44/0.54    inference(forward_demodulation,[],[f163,f138])).
% 1.44/0.54  fof(f163,plain,(
% 1.44/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~spl3_7),
% 1.44/0.54    inference(forward_demodulation,[],[f162,f141])).
% 1.44/0.54  fof(f162,plain,(
% 1.44/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_7),
% 1.44/0.54    inference(subsumption_resolution,[],[f155,f115])).
% 1.44/0.54  fof(f155,plain,(
% 1.44/0.54    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.44/0.54    inference(resolution,[],[f128,f46])).
% 1.44/0.54  fof(f46,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f18])).
% 1.44/0.54  fof(f181,plain,(
% 1.44/0.54    spl3_8 | spl3_9),
% 1.44/0.54    inference(avatar_split_clause,[],[f172,f178,f174])).
% 1.44/0.54  fof(f172,plain,(
% 1.44/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.44/0.54    inference(subsumption_resolution,[],[f169,f40])).
% 1.44/0.54  fof(f169,plain,(
% 1.44/0.54    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.44/0.54    inference(resolution,[],[f67,f41])).
% 1.44/0.54  fof(f67,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.44/0.54    inference(cnf_transformation,[],[f38])).
% 1.44/0.54  fof(f127,plain,(
% 1.44/0.54    spl3_1),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f126])).
% 1.44/0.54  fof(f126,plain,(
% 1.44/0.54    $false | spl3_1),
% 1.44/0.54    inference(subsumption_resolution,[],[f125,f120])).
% 1.44/0.54  fof(f125,plain,(
% 1.44/0.54    ~v1_relat_1(sK2) | spl3_1),
% 1.44/0.54    inference(subsumption_resolution,[],[f117,f85])).
% 1.44/0.54  fof(f85,plain,(
% 1.44/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 1.44/0.54    inference(avatar_component_clause,[],[f83])).
% 1.44/0.54  fof(f83,plain,(
% 1.44/0.54    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.54  fof(f124,plain,(
% 1.44/0.54    spl3_6),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f123])).
% 1.44/0.54  fof(f123,plain,(
% 1.44/0.54    $false | spl3_6),
% 1.44/0.54    inference(subsumption_resolution,[],[f120,f111])).
% 1.44/0.54  fof(f111,plain,(
% 1.44/0.54    ~v1_relat_1(sK2) | spl3_6),
% 1.44/0.54    inference(avatar_component_clause,[],[f109])).
% 1.44/0.54  fof(f109,plain,(
% 1.44/0.54    spl3_6 <=> v1_relat_1(sK2)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.44/0.54  fof(f116,plain,(
% 1.44/0.54    ~spl3_6 | spl3_7),
% 1.44/0.54    inference(avatar_split_clause,[],[f107,f113,f109])).
% 1.44/0.54  fof(f107,plain,(
% 1.44/0.54    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f48,f39])).
% 1.44/0.54  fof(f48,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f20])).
% 1.44/0.54  fof(f94,plain,(
% 1.44/0.54    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.44/0.54    inference(avatar_split_clause,[],[f44,f91,f87,f83])).
% 1.44/0.54  fof(f44,plain,(
% 1.44/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  % SZS output end Proof for theBenchmark
% 1.44/0.54  % (14935)------------------------------
% 1.44/0.54  % (14935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (14935)Termination reason: Refutation
% 1.44/0.54  
% 1.44/0.54  % (14935)Memory used [KB]: 10874
% 1.44/0.54  % (14935)Time elapsed: 0.140 s
% 1.44/0.54  % (14935)------------------------------
% 1.44/0.54  % (14935)------------------------------
% 1.44/0.54  % (14950)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.44/0.54  % (14944)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.44/0.55  % (14941)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.61/0.56  % (14924)Success in time 0.198 s
%------------------------------------------------------------------------------
