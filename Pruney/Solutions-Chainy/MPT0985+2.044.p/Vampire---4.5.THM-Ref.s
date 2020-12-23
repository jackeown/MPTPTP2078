%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 518 expanded)
%              Number of leaves         :   20 ( 133 expanded)
%              Depth                    :   16
%              Number of atoms          :  363 (2608 expanded)
%              Number of equality atoms :   79 ( 420 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f94,f300,f302,f354,f373])).

fof(f373,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f371,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f39])).

fof(f39,plain,
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

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f371,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_3 ),
    inference(resolution,[],[f368,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f60,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f368,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f367,f96])).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f90,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f90,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f51,f44])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f367,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f366,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f366,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f365,f45])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f365,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(superposition,[],[f85,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f85,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f354,plain,
    ( spl3_2
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f339,f343])).

fof(f343,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f330,f337])).

fof(f337,plain,
    ( k1_xboole_0 = sK1
    | spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f330,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f330,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl3_2
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f324,f49])).

fof(f49,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(f324,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),sK1,k1_xboole_0)
    | spl3_2
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f308,f314])).

fof(f314,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f313,f96])).

fof(f313,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f307,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v4_relat_1(X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f58,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f307,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f97,f229])).

fof(f229,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl3_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f97,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f308,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,k1_xboole_0)
    | spl3_2
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f110,f229])).

fof(f110,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f109,f96])).

fof(f109,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f108,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f105,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(superposition,[],[f82,f54])).

fof(f82,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f339,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f319,f337])).

fof(f319,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f303,f314])).

fof(f303,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f43,f229])).

fof(f43,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f302,plain,
    ( spl3_12
    | spl3_13 ),
    inference(avatar_split_clause,[],[f301,f231,f228])).

fof(f231,plain,
    ( spl3_13
  <=> v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f301,plain,
    ( v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f279,f44])).

fof(f279,plain,
    ( v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(trivial_inequality_removal,[],[f278])).

fof(f278,plain,
    ( sK1 != sK1
    | v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f160,f46])).

fof(f46,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X1,X0,X2) != X0
      | v1_funct_2(k3_relset_1(X1,X0,X2),X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f157,f60])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X1,X0,X2) != X0
      | v1_funct_2(k3_relset_1(X1,X0,X2),X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(k3_relset_1(X1,X0,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(superposition,[],[f66,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2)
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2)
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f300,plain,
    ( spl3_2
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f298,f44])).

fof(f298,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f297,f110])).

fof(f297,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_13 ),
    inference(superposition,[],[f232,f59])).

fof(f232,plain,
    ( v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f231])).

fof(f94,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f92,f55])).

fof(f92,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f90,f89])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f88,f42])).

fof(f88,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f53,f79])).

fof(f79,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

% (11063)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f86,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f47,f84,f81,f78])).

fof(f47,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:55:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (11059)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (11046)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (11062)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (11048)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (11058)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (11053)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (11066)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (11051)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (11065)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (11048)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (11050)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.53  % (11064)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  % (11056)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.53  % (11049)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (11047)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (11049)Refutation not found, incomplete strategy% (11049)------------------------------
% 0.20/0.53  % (11049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11049)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11049)Memory used [KB]: 10618
% 0.20/0.53  % (11049)Time elapsed: 0.111 s
% 0.20/0.53  % (11049)------------------------------
% 0.20/0.53  % (11049)------------------------------
% 0.20/0.53  % (11047)Refutation not found, incomplete strategy% (11047)------------------------------
% 0.20/0.53  % (11047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11047)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11047)Memory used [KB]: 10618
% 0.20/0.53  % (11047)Time elapsed: 0.109 s
% 0.20/0.53  % (11047)------------------------------
% 0.20/0.53  % (11047)------------------------------
% 0.20/0.53  % (11066)Refutation not found, incomplete strategy% (11066)------------------------------
% 0.20/0.53  % (11066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11066)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11066)Memory used [KB]: 10618
% 0.20/0.53  % (11066)Time elapsed: 0.125 s
% 0.20/0.53  % (11066)------------------------------
% 0.20/0.53  % (11066)------------------------------
% 0.20/0.54  % (11054)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.54  % (11057)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f374,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f86,f94,f300,f302,f354,f373])).
% 0.20/0.54  fof(f373,plain,(
% 0.20/0.54    spl3_3),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f372])).
% 0.20/0.54  fof(f372,plain,(
% 0.20/0.54    $false | spl3_3),
% 0.20/0.54    inference(subsumption_resolution,[],[f371,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f17])).
% 0.20/0.54  fof(f17,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.54  fof(f371,plain,(
% 0.20/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_3),
% 0.20/0.54    inference(resolution,[],[f368,f124])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k4_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k4_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(superposition,[],[f60,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.20/0.54  fof(f368,plain,(
% 0.20/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.20/0.54    inference(subsumption_resolution,[],[f367,f96])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f90,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.54    inference(resolution,[],[f51,f44])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.54  fof(f367,plain,(
% 0.20/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(sK2) | spl3_3),
% 0.20/0.54    inference(subsumption_resolution,[],[f366,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    v1_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f366,plain,(
% 0.20/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_3),
% 0.20/0.54    inference(subsumption_resolution,[],[f365,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    v2_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f365,plain,(
% 0.20/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_3),
% 0.20/0.54    inference(superposition,[],[f85,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.54  fof(f354,plain,(
% 0.20/0.54    spl3_2 | ~spl3_12),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f353])).
% 0.20/0.54  fof(f353,plain,(
% 0.20/0.54    $false | (spl3_2 | ~spl3_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f339,f343])).
% 0.20/0.54  fof(f343,plain,(
% 0.20/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_12)),
% 0.20/0.54    inference(backward_demodulation,[],[f330,f337])).
% 0.20/0.54  fof(f337,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | (spl3_2 | ~spl3_12)),
% 0.20/0.54    inference(resolution,[],[f330,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f73,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.20/0.54    inference(equality_resolution,[],[f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(equality_resolution,[],[f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.54  fof(f330,plain,(
% 0.20/0.54    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (spl3_2 | ~spl3_12)),
% 0.20/0.54    inference(forward_demodulation,[],[f324,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
% 0.20/0.54  fof(f324,plain,(
% 0.20/0.54    ~v1_funct_2(k4_relat_1(k1_xboole_0),sK1,k1_xboole_0) | (spl3_2 | ~spl3_12)),
% 0.20/0.54    inference(backward_demodulation,[],[f308,f314])).
% 0.20/0.54  fof(f314,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~spl3_12),
% 0.20/0.54    inference(subsumption_resolution,[],[f313,f96])).
% 0.20/0.54  fof(f313,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl3_12),
% 0.20/0.54    inference(resolution,[],[f307,f102])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    ( ! [X0] : (~v4_relat_1(X0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(superposition,[],[f58,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.54  fof(f307,plain,(
% 0.20/0.54    v4_relat_1(sK2,k1_xboole_0) | ~spl3_12),
% 0.20/0.54    inference(backward_demodulation,[],[f97,f229])).
% 0.20/0.54  fof(f229,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | ~spl3_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f228])).
% 0.20/0.54  fof(f228,plain,(
% 0.20/0.54    spl3_12 <=> k1_xboole_0 = sK0),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    v4_relat_1(sK2,sK0)),
% 0.20/0.54    inference(resolution,[],[f61,f44])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.54  fof(f308,plain,(
% 0.20/0.54    ~v1_funct_2(k4_relat_1(sK2),sK1,k1_xboole_0) | (spl3_2 | ~spl3_12)),
% 0.20/0.54    inference(backward_demodulation,[],[f110,f229])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f109,f96])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_relat_1(sK2) | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f108,f42])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f105,f45])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_2),
% 0.20/0.54    inference(superposition,[],[f82,f54])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.54  fof(f339,plain,(
% 0.20/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_12)),
% 0.20/0.54    inference(backward_demodulation,[],[f319,f337])).
% 0.20/0.54  fof(f319,plain,(
% 0.20/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~spl3_12),
% 0.20/0.54    inference(backward_demodulation,[],[f303,f314])).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl3_12),
% 0.20/0.54    inference(backward_demodulation,[],[f43,f229])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f302,plain,(
% 0.20/0.54    spl3_12 | spl3_13),
% 0.20/0.54    inference(avatar_split_clause,[],[f301,f231,f228])).
% 0.20/0.54  fof(f231,plain,(
% 0.20/0.54    spl3_13 <=> v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0) | k1_xboole_0 = sK0),
% 0.20/0.54    inference(subsumption_resolution,[],[f279,f44])).
% 0.20/0.54  fof(f279,plain,(
% 0.20/0.54    v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f278])).
% 0.20/0.54  fof(f278,plain,(
% 0.20/0.54    sK1 != sK1 | v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.54    inference(superposition,[],[f160,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X1,X0,X2) != X0 | v1_funct_2(k3_relset_1(X1,X0,X2),X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f157,f60])).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X1,X0,X2) != X0 | v1_funct_2(k3_relset_1(X1,X0,X2),X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(k3_relset_1(X1,X0,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.54    inference(superposition,[],[f66,f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f300,plain,(
% 0.20/0.54    spl3_2 | ~spl3_13),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f299])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    $false | (spl3_2 | ~spl3_13)),
% 0.20/0.54    inference(subsumption_resolution,[],[f298,f44])).
% 0.20/0.54  fof(f298,plain,(
% 0.20/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl3_2 | ~spl3_13)),
% 0.20/0.54    inference(subsumption_resolution,[],[f297,f110])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_13),
% 0.20/0.54    inference(superposition,[],[f232,f59])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    v1_funct_2(k3_relset_1(sK0,sK1,sK2),sK1,sK0) | ~spl3_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f231])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    spl3_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    $false | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f92,f55])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f90,f89])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f88,f42])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.20/0.54    inference(resolution,[],[f53,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f24])).
% 0.20/0.54  % (11063)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f47,f84,f81,f78])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (11048)------------------------------
% 0.20/0.54  % (11048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11048)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (11048)Memory used [KB]: 10746
% 0.20/0.54  % (11048)Time elapsed: 0.093 s
% 0.20/0.54  % (11048)------------------------------
% 0.20/0.54  % (11048)------------------------------
% 0.20/0.54  % (11061)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.54  % (11045)Success in time 0.191 s
%------------------------------------------------------------------------------
