%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:37 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  235 (1774 expanded)
%              Number of leaves         :   26 ( 423 expanded)
%              Depth                    :   24
%              Number of atoms          :  653 (7956 expanded)
%              Number of equality atoms :  156 (2295 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3736,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f101,f115,f177,f206,f283,f310,f571,f577,f982,f1058,f1147,f3498,f3584,f3731,f3733])).

fof(f3733,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f3732])).

fof(f3732,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f91,f624])).

fof(f624,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f268,f143])).

fof(f143,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f142,f122])).

fof(f122,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f121,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f29])).

fof(f29,plain,
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f142,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f139,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f139,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f63,f41])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f268,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(subsumption_resolution,[],[f264,f122])).

fof(f264,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f210,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f210,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(superposition,[],[f42,f152])).

fof(f152,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f62,f41])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f42,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f3731,plain,
    ( ~ spl4_11
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f3730])).

fof(f3730,plain,
    ( $false
    | ~ spl4_11
    | spl4_37 ),
    inference(global_subsumption,[],[f44,f39,f624,f3721,f1433])).

fof(f1433,plain,
    ( k1_xboole_0 != sK2
    | spl4_37 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1432,plain,
    ( spl4_37
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f3721,plain,
    ( v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f3720,f176])).

fof(f176,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_11
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f3720,plain,
    ( k1_xboole_0 = sK2
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f3719,f1417])).

fof(f1417,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1309,f176])).

fof(f1309,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f624,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f3719,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1463,f176])).

fof(f1463,plain,
    ( k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f626,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f626,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(resolution,[],[f268,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f3584,plain,
    ( spl4_5
    | ~ spl4_11
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f3583])).

fof(f3583,plain,
    ( $false
    | spl4_5
    | ~ spl4_11
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f3582,f99])).

fof(f99,plain,
    ( k1_xboole_0 != sK0
    | spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f3582,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_11
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(trivial_inequality_removal,[],[f3581])).

fof(f3581,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ spl4_11
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(duplicate_literal_removal,[],[f3507])).

fof(f3507,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ spl4_11
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(superposition,[],[f56,f3500])).

fof(f3500,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl4_11
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f3499,f2954])).

fof(f2954,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(resolution,[],[f2733,f634])).

fof(f634,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_relat_1(k1_xboole_0))
      | k1_relat_1(k1_xboole_0) = X2 ) ),
    inference(resolution,[],[f276,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f276,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f275,f116])).

fof(f116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f275,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f234,f47])).

fof(f234,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f140,f120])).

fof(f120,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f55,f71])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f63,f73])).

fof(f2733,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f2732,f176])).

fof(f2732,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK3),X0)
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f2730,f122])).

fof(f2730,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(sK3),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_37 ),
    inference(resolution,[],[f2121,f47])).

fof(f2121,plain,
    ( ! [X1] : v4_relat_1(sK3,X1)
    | ~ spl4_37 ),
    inference(resolution,[],[f1503,f140])).

fof(f1503,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f1491,f73])).

fof(f1491,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | ~ spl4_37 ),
    inference(superposition,[],[f626,f1434])).

fof(f1434,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f3499,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f981,f986])).

fof(f986,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f634,f280])).

fof(f280,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f279,f116])).

fof(f279,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f236,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f236,plain,(
    ! [X0] : v5_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f146,f120])).

fof(f146,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v5_relat_1(X3,X2) ) ),
    inference(superposition,[],[f64,f74])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f981,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f979])).

fof(f979,plain,
    ( spl4_34
  <=> k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3498,plain,
    ( ~ spl4_11
    | spl4_33
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f3497])).

fof(f3497,plain,
    ( $false
    | ~ spl4_11
    | spl4_33
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f3472,f3438])).

fof(f3438,plain,
    ( ! [X17] : r1_tarski(k2_zfmisc_1(sK0,X17),k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(resolution,[],[f3001,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3001,plain,
    ( ! [X1] : m1_subset_1(k2_zfmisc_1(sK0,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f2988,f2954])).

fof(f2988,plain,(
    ! [X1] : m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f2026,f74])).

fof(f2026,plain,(
    ! [X6,X7] : m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X6),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) ),
    inference(subsumption_resolution,[],[f2017,f276])).

fof(f2017,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X7)
      | m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X6),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) ) ),
    inference(superposition,[],[f694,f985])).

fof(f985,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k1_relat_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X0)) ),
    inference(resolution,[],[f634,f290])).

fof(f290,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(subsumption_resolution,[],[f287,f46])).

fof(f287,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)
      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f217,f47])).

fof(f217,plain,(
    ! [X8,X9] : v4_relat_1(k2_zfmisc_1(X8,X9),X8) ),
    inference(resolution,[],[f120,f63])).

fof(f694,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X2)
      | m1_subset_1(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(subsumption_resolution,[],[f688,f46])).

fof(f688,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X2)
      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f294,f59])).

fof(f294,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(subsumption_resolution,[],[f291,f46])).

fof(f291,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)
      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f218,f49])).

fof(f218,plain,(
    ! [X10,X11] : v5_relat_1(k2_zfmisc_1(X10,X11),X11) ),
    inference(resolution,[],[f120,f64])).

fof(f3472,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),k1_xboole_0)
    | ~ spl4_11
    | spl4_33
    | ~ spl4_37 ),
    inference(superposition,[],[f1916,f2954])).

fof(f1916,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)),k1_xboole_0)
    | spl4_33 ),
    inference(superposition,[],[f977,f986])).

fof(f977,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)),k1_xboole_0)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f975])).

fof(f975,plain,
    ( spl4_33
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1147,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f1146])).

fof(f1146,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f1109,f305])).

fof(f305,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl4_18
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1109,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(superposition,[],[f432,f1064])).

fof(f1064,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f597,f997])).

fof(f997,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f996,f580])).

fof(f580,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f539,f579])).

fof(f579,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f171,f100])).

fof(f100,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f171,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_10
  <=> r1_tarski(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f539,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5 ),
    inference(resolution,[],[f439,f53])).

fof(f439,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f143,f100])).

fof(f996,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK3),X0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f995,f122])).

fof(f995,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(sK3),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_5 ),
    inference(resolution,[],[f724,f47])).

fof(f724,plain,
    ( ! [X1] : v4_relat_1(sK3,X1)
    | ~ spl4_5 ),
    inference(resolution,[],[f542,f140])).

fof(f542,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f541,f74])).

fof(f541,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))))
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f537,f122])).

fof(f537,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f439,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f59,f71])).

fof(f597,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f452,f53])).

fof(f452,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f434,f74])).

fof(f434,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f118,f100])).

fof(f118,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f54,f41])).

fof(f432,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f87,f100])).

fof(f87,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1058,plain,
    ( ~ spl4_5
    | ~ spl4_10
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f1057])).

fof(f1057,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_10
    | spl4_19 ),
    inference(subsumption_resolution,[],[f1056,f309])).

fof(f309,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl4_19
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1056,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f1047,f74])).

fof(f1047,plain,
    ( ! [X2] : k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X2))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(resolution,[],[f997,f681])).

fof(f681,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,k1_relat_1(k2_zfmisc_1(X4,X5)))
      | k1_relat_1(k2_zfmisc_1(X4,X5)) = X4 ) ),
    inference(resolution,[],[f290,f53])).

fof(f982,plain,
    ( ~ spl4_33
    | spl4_34 ),
    inference(avatar_split_clause,[],[f972,f979,f975])).

fof(f972,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f705,f53])).

fof(f705,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f317,f54])).

fof(f317,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))) ),
    inference(resolution,[],[f257,f116])).

fof(f257,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(resolution,[],[f157,f71])).

fof(f577,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f529,f432])).

fof(f529,plain,
    ( ! [X0] : v1_funct_2(sK3,k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f524,f496])).

fof(f496,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f468,f414])).

fof(f414,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f400,f100])).

fof(f400,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl4_4 ),
    inference(superposition,[],[f149,f95])).

fof(f95,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f149,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f61,f41])).

fof(f468,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f463,f408])).

fof(f408,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f393,f73])).

fof(f393,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f41,f95])).

fof(f463,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f407,f113])).

fof(f113,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f79,f74])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f407,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f392,f100])).

fof(f392,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(superposition,[],[f40,f95])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f524,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(sK3)
        | v1_funct_2(sK3,k1_xboole_0,X0) )
    | ~ spl4_4 ),
    inference(superposition,[],[f471,f477])).

fof(f477,plain,
    ( ! [X4] : k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,X4,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f408,f151])).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f61,f74])).

fof(f471,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,sK3)
        | v1_funct_2(sK3,k1_xboole_0,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f408,f112])).

fof(f112,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f78,f74])).

fof(f78,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f571,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | spl4_10 ),
    inference(subsumption_resolution,[],[f564,f71])).

fof(f564,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_10 ),
    inference(superposition,[],[f423,f496])).

fof(f423,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | spl4_10 ),
    inference(forward_demodulation,[],[f172,f100])).

fof(f172,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f310,plain,
    ( spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f301,f307,f304])).

fof(f301,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f221,f253])).

fof(f253,plain,(
    ! [X0] : k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f151,f120])).

fof(f221,plain,(
    ! [X16] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X16,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X16) ) ),
    inference(resolution,[],[f120,f112])).

fof(f283,plain,
    ( spl4_4
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f281,f71])).

fof(f281,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_4
    | spl4_10 ),
    inference(superposition,[],[f172,f202])).

fof(f202,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f162,f149])).

fof(f162,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f161,f96])).

fof(f96,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f161,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f158,f40])).

fof(f158,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f65,f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f206,plain,
    ( spl4_4
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f202,f175])).

fof(f175,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f177,plain,
    ( ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f167,f174,f170])).

fof(f167,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3)) ),
    inference(resolution,[],[f143,f53])).

fof(f115,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f83,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f101,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f43,f98,f94])).

fof(f43,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f44,f89,f85,f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (29366)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (29377)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (29390)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (29369)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (29376)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (29367)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (29388)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (29378)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (29380)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (29368)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (29386)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (29367)Refutation not found, incomplete strategy% (29367)------------------------------
% 0.22/0.52  % (29367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29391)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (29370)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (29385)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (29375)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (29367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (29367)Memory used [KB]: 10618
% 0.22/0.52  % (29367)Time elapsed: 0.102 s
% 0.22/0.52  % (29367)------------------------------
% 0.22/0.52  % (29367)------------------------------
% 0.22/0.52  % (29384)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (29387)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.31/0.53  % (29371)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.31/0.53  % (29372)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.31/0.53  % (29373)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.31/0.53  % (29371)Refutation not found, incomplete strategy% (29371)------------------------------
% 1.31/0.53  % (29371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (29371)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (29371)Memory used [KB]: 6268
% 1.31/0.53  % (29371)Time elapsed: 0.114 s
% 1.31/0.53  % (29371)------------------------------
% 1.31/0.53  % (29371)------------------------------
% 1.31/0.53  % (29382)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.31/0.53  % (29372)Refutation not found, incomplete strategy% (29372)------------------------------
% 1.31/0.53  % (29372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (29372)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (29372)Memory used [KB]: 10618
% 1.31/0.53  % (29372)Time elapsed: 0.073 s
% 1.31/0.53  % (29372)------------------------------
% 1.31/0.53  % (29372)------------------------------
% 1.31/0.53  % (29389)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.31/0.54  % (29383)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.31/0.54  % (29374)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.50/0.55  % (29379)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.50/0.55  % (29381)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.50/0.62  % (29375)Refutation not found, incomplete strategy% (29375)------------------------------
% 1.50/0.62  % (29375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.62  % (29375)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.62  
% 1.50/0.62  % (29375)Memory used [KB]: 6268
% 1.50/0.62  % (29375)Time elapsed: 0.212 s
% 1.50/0.62  % (29375)------------------------------
% 1.50/0.62  % (29375)------------------------------
% 2.16/0.67  % (29376)Refutation found. Thanks to Tanya!
% 2.16/0.67  % SZS status Theorem for theBenchmark
% 2.16/0.67  % SZS output start Proof for theBenchmark
% 2.16/0.67  fof(f3736,plain,(
% 2.16/0.67    $false),
% 2.16/0.67    inference(avatar_sat_refutation,[],[f92,f101,f115,f177,f206,f283,f310,f571,f577,f982,f1058,f1147,f3498,f3584,f3731,f3733])).
% 2.16/0.67  fof(f3733,plain,(
% 2.16/0.67    spl4_3),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f3732])).
% 2.16/0.67  fof(f3732,plain,(
% 2.16/0.67    $false | spl4_3),
% 2.16/0.67    inference(subsumption_resolution,[],[f91,f624])).
% 2.16/0.67  fof(f624,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.16/0.67    inference(resolution,[],[f268,f143])).
% 2.16/0.67  fof(f143,plain,(
% 2.16/0.67    r1_tarski(k1_relat_1(sK3),sK0)),
% 2.16/0.67    inference(subsumption_resolution,[],[f142,f122])).
% 2.16/0.67  fof(f122,plain,(
% 2.16/0.67    v1_relat_1(sK3)),
% 2.16/0.67    inference(subsumption_resolution,[],[f121,f46])).
% 2.16/0.67  fof(f46,plain,(
% 2.16/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f7])).
% 2.16/0.67  fof(f7,axiom,(
% 2.16/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.16/0.67  fof(f121,plain,(
% 2.16/0.67    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.16/0.67    inference(resolution,[],[f45,f41])).
% 2.16/0.67  fof(f41,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.16/0.67    inference(cnf_transformation,[],[f30])).
% 2.16/0.67  fof(f30,plain,(
% 2.16/0.67    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.16/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f29])).
% 2.16/0.67  fof(f29,plain,(
% 2.16/0.67    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.16/0.67    introduced(choice_axiom,[])).
% 2.16/0.67  fof(f17,plain,(
% 2.16/0.67    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.16/0.67    inference(flattening,[],[f16])).
% 2.16/0.67  fof(f16,plain,(
% 2.16/0.67    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.16/0.67    inference(ennf_transformation,[],[f15])).
% 2.16/0.67  fof(f15,negated_conjecture,(
% 2.16/0.67    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.16/0.67    inference(negated_conjecture,[],[f14])).
% 2.16/0.67  fof(f14,conjecture,(
% 2.16/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 2.16/0.67  fof(f45,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f18])).
% 2.16/0.67  fof(f18,plain,(
% 2.16/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f4])).
% 2.16/0.67  fof(f4,axiom,(
% 2.16/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.16/0.67  fof(f142,plain,(
% 2.16/0.67    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 2.16/0.67    inference(resolution,[],[f139,f47])).
% 2.16/0.67  fof(f47,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f31])).
% 2.16/0.67  fof(f31,plain,(
% 2.16/0.67    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(nnf_transformation,[],[f19])).
% 2.16/0.67  fof(f19,plain,(
% 2.16/0.67    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(ennf_transformation,[],[f5])).
% 2.16/0.67  fof(f5,axiom,(
% 2.16/0.67    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.16/0.67  fof(f139,plain,(
% 2.16/0.67    v4_relat_1(sK3,sK0)),
% 2.16/0.67    inference(resolution,[],[f63,f41])).
% 2.16/0.67  fof(f63,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f26])).
% 2.16/0.67  fof(f26,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f9])).
% 2.16/0.67  fof(f9,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.16/0.67  fof(f268,plain,(
% 2.16/0.67    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f264,f122])).
% 2.16/0.67  fof(f264,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 2.16/0.67    inference(resolution,[],[f210,f59])).
% 2.16/0.67  fof(f59,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f22])).
% 2.16/0.67  fof(f22,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.16/0.67    inference(flattening,[],[f21])).
% 2.16/0.67  fof(f21,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.16/0.67    inference(ennf_transformation,[],[f12])).
% 2.16/0.67  fof(f12,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 2.16/0.67  fof(f210,plain,(
% 2.16/0.67    r1_tarski(k2_relat_1(sK3),sK2)),
% 2.16/0.67    inference(superposition,[],[f42,f152])).
% 2.16/0.67  fof(f152,plain,(
% 2.16/0.67    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 2.16/0.67    inference(resolution,[],[f62,f41])).
% 2.16/0.67  fof(f62,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f25])).
% 2.16/0.67  fof(f25,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f11])).
% 2.16/0.67  fof(f11,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.16/0.67  fof(f42,plain,(
% 2.16/0.67    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 2.16/0.67    inference(cnf_transformation,[],[f30])).
% 2.16/0.67  fof(f91,plain,(
% 2.16/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_3),
% 2.16/0.67    inference(avatar_component_clause,[],[f89])).
% 2.16/0.67  fof(f89,plain,(
% 2.16/0.67    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.16/0.67  fof(f3731,plain,(
% 2.16/0.67    ~spl4_11 | spl4_37),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f3730])).
% 2.16/0.67  fof(f3730,plain,(
% 2.16/0.67    $false | (~spl4_11 | spl4_37)),
% 2.16/0.67    inference(global_subsumption,[],[f44,f39,f624,f3721,f1433])).
% 2.16/0.67  fof(f1433,plain,(
% 2.16/0.67    k1_xboole_0 != sK2 | spl4_37),
% 2.16/0.67    inference(avatar_component_clause,[],[f1432])).
% 2.16/0.67  fof(f1432,plain,(
% 2.16/0.67    spl4_37 <=> k1_xboole_0 = sK2),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.16/0.67  fof(f3721,plain,(
% 2.16/0.67    v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK2 | ~spl4_11),
% 2.16/0.67    inference(forward_demodulation,[],[f3720,f176])).
% 2.16/0.67  fof(f176,plain,(
% 2.16/0.67    sK0 = k1_relat_1(sK3) | ~spl4_11),
% 2.16/0.67    inference(avatar_component_clause,[],[f174])).
% 2.16/0.67  fof(f174,plain,(
% 2.16/0.67    spl4_11 <=> sK0 = k1_relat_1(sK3)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.16/0.67  fof(f3720,plain,(
% 2.16/0.67    k1_xboole_0 = sK2 | v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~spl4_11),
% 2.16/0.67    inference(subsumption_resolution,[],[f3719,f1417])).
% 2.16/0.67  fof(f1417,plain,(
% 2.16/0.67    sK0 = k1_relset_1(sK0,sK2,sK3) | ~spl4_11),
% 2.16/0.67    inference(forward_demodulation,[],[f1309,f176])).
% 2.16/0.67  fof(f1309,plain,(
% 2.16/0.67    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 2.16/0.67    inference(resolution,[],[f624,f61])).
% 2.16/0.67  fof(f61,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f24])).
% 2.16/0.67  fof(f24,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f10])).
% 2.16/0.67  fof(f10,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.16/0.67  fof(f3719,plain,(
% 2.16/0.67    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~spl4_11),
% 2.16/0.67    inference(forward_demodulation,[],[f1463,f176])).
% 2.16/0.67  fof(f1463,plain,(
% 2.16/0.67    k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 2.16/0.67    inference(resolution,[],[f626,f67])).
% 2.16/0.67  fof(f67,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f38])).
% 2.16/0.67  fof(f38,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(nnf_transformation,[],[f28])).
% 2.16/0.67  fof(f28,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(flattening,[],[f27])).
% 2.16/0.67  fof(f27,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f13])).
% 2.16/0.67  fof(f13,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.16/0.67  fof(f626,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 2.16/0.67    inference(resolution,[],[f268,f71])).
% 2.16/0.67  fof(f71,plain,(
% 2.16/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.16/0.67    inference(equality_resolution,[],[f52])).
% 2.16/0.67  fof(f52,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.16/0.67    inference(cnf_transformation,[],[f34])).
% 2.16/0.67  fof(f34,plain,(
% 2.16/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/0.67    inference(flattening,[],[f33])).
% 2.16/0.67  fof(f33,plain,(
% 2.16/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/0.67    inference(nnf_transformation,[],[f1])).
% 2.16/0.67  fof(f1,axiom,(
% 2.16/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.16/0.67  fof(f39,plain,(
% 2.16/0.67    v1_funct_1(sK3)),
% 2.16/0.67    inference(cnf_transformation,[],[f30])).
% 2.16/0.67  fof(f44,plain,(
% 2.16/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.16/0.67    inference(cnf_transformation,[],[f30])).
% 2.16/0.67  fof(f3584,plain,(
% 2.16/0.67    spl4_5 | ~spl4_11 | ~spl4_34 | ~spl4_37),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f3583])).
% 2.16/0.67  fof(f3583,plain,(
% 2.16/0.67    $false | (spl4_5 | ~spl4_11 | ~spl4_34 | ~spl4_37)),
% 2.16/0.67    inference(subsumption_resolution,[],[f3582,f99])).
% 2.16/0.67  fof(f99,plain,(
% 2.16/0.67    k1_xboole_0 != sK0 | spl4_5),
% 2.16/0.67    inference(avatar_component_clause,[],[f98])).
% 2.16/0.67  fof(f98,plain,(
% 2.16/0.67    spl4_5 <=> k1_xboole_0 = sK0),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.16/0.67  fof(f3582,plain,(
% 2.16/0.67    k1_xboole_0 = sK0 | (~spl4_11 | ~spl4_34 | ~spl4_37)),
% 2.16/0.67    inference(trivial_inequality_removal,[],[f3581])).
% 2.16/0.67  fof(f3581,plain,(
% 2.16/0.67    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | (~spl4_11 | ~spl4_34 | ~spl4_37)),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f3507])).
% 2.16/0.67  fof(f3507,plain,(
% 2.16/0.67    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | (~spl4_11 | ~spl4_34 | ~spl4_37)),
% 2.16/0.67    inference(superposition,[],[f56,f3500])).
% 2.16/0.67  fof(f3500,plain,(
% 2.16/0.67    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | (~spl4_11 | ~spl4_34 | ~spl4_37)),
% 2.16/0.67    inference(forward_demodulation,[],[f3499,f2954])).
% 2.16/0.67  fof(f2954,plain,(
% 2.16/0.67    sK0 = k1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_37)),
% 2.16/0.67    inference(resolution,[],[f2733,f634])).
% 2.16/0.67  fof(f634,plain,(
% 2.16/0.67    ( ! [X2] : (~r1_tarski(X2,k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0) = X2) )),
% 2.16/0.67    inference(resolution,[],[f276,f53])).
% 2.16/0.67  fof(f53,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f34])).
% 2.16/0.67  fof(f276,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f275,f116])).
% 2.16/0.67  fof(f116,plain,(
% 2.16/0.67    v1_relat_1(k1_xboole_0)),
% 2.16/0.67    inference(superposition,[],[f46,f73])).
% 2.16/0.67  fof(f73,plain,(
% 2.16/0.67    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.16/0.67    inference(equality_resolution,[],[f58])).
% 2.16/0.67  fof(f58,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.16/0.67    inference(cnf_transformation,[],[f37])).
% 2.16/0.67  fof(f37,plain,(
% 2.16/0.67    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.16/0.67    inference(flattening,[],[f36])).
% 2.16/0.67  fof(f36,plain,(
% 2.16/0.67    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.16/0.67    inference(nnf_transformation,[],[f2])).
% 2.16/0.67  fof(f2,axiom,(
% 2.16/0.67    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.16/0.67  fof(f275,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 2.16/0.67    inference(resolution,[],[f234,f47])).
% 2.16/0.67  fof(f234,plain,(
% 2.16/0.67    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 2.16/0.67    inference(resolution,[],[f140,f120])).
% 2.16/0.67  fof(f120,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.16/0.67    inference(resolution,[],[f55,f71])).
% 2.16/0.67  fof(f55,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f35])).
% 2.16/0.67  fof(f35,plain,(
% 2.16/0.67    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.16/0.67    inference(nnf_transformation,[],[f3])).
% 2.16/0.67  fof(f3,axiom,(
% 2.16/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.16/0.67  fof(f140,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 2.16/0.67    inference(superposition,[],[f63,f73])).
% 2.16/0.67  fof(f2733,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(sK0,X0)) ) | (~spl4_11 | ~spl4_37)),
% 2.16/0.67    inference(forward_demodulation,[],[f2732,f176])).
% 2.16/0.67  fof(f2732,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(sK3),X0)) ) | ~spl4_37),
% 2.16/0.67    inference(subsumption_resolution,[],[f2730,f122])).
% 2.16/0.67  fof(f2730,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) ) | ~spl4_37),
% 2.16/0.67    inference(resolution,[],[f2121,f47])).
% 2.16/0.67  fof(f2121,plain,(
% 2.16/0.67    ( ! [X1] : (v4_relat_1(sK3,X1)) ) | ~spl4_37),
% 2.16/0.67    inference(resolution,[],[f1503,f140])).
% 2.16/0.67  fof(f1503,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_37),
% 2.16/0.67    inference(forward_demodulation,[],[f1491,f73])).
% 2.16/0.67  fof(f1491,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) | ~spl4_37),
% 2.16/0.67    inference(superposition,[],[f626,f1434])).
% 2.16/0.67  fof(f1434,plain,(
% 2.16/0.67    k1_xboole_0 = sK2 | ~spl4_37),
% 2.16/0.67    inference(avatar_component_clause,[],[f1432])).
% 2.16/0.67  fof(f3499,plain,(
% 2.16/0.67    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~spl4_34),
% 2.16/0.67    inference(forward_demodulation,[],[f981,f986])).
% 2.16/0.67  fof(f986,plain,(
% 2.16/0.67    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 2.16/0.67    inference(resolution,[],[f634,f280])).
% 2.16/0.67  fof(f280,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f279,f116])).
% 2.16/0.67  fof(f279,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 2.16/0.67    inference(resolution,[],[f236,f49])).
% 2.16/0.67  fof(f49,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f32])).
% 2.16/0.67  fof(f32,plain,(
% 2.16/0.67    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(nnf_transformation,[],[f20])).
% 2.16/0.67  fof(f20,plain,(
% 2.16/0.67    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(ennf_transformation,[],[f6])).
% 2.16/0.67  fof(f6,axiom,(
% 2.16/0.67    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.16/0.67  fof(f236,plain,(
% 2.16/0.67    ( ! [X0] : (v5_relat_1(k1_xboole_0,X0)) )),
% 2.16/0.67    inference(resolution,[],[f146,f120])).
% 2.16/0.67  fof(f146,plain,(
% 2.16/0.67    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v5_relat_1(X3,X2)) )),
% 2.16/0.67    inference(superposition,[],[f64,f74])).
% 2.16/0.67  fof(f74,plain,(
% 2.16/0.67    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.16/0.67    inference(equality_resolution,[],[f57])).
% 2.16/0.67  fof(f57,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f37])).
% 2.16/0.67  fof(f64,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f26])).
% 2.16/0.67  fof(f981,plain,(
% 2.16/0.67    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~spl4_34),
% 2.16/0.67    inference(avatar_component_clause,[],[f979])).
% 2.16/0.67  fof(f979,plain,(
% 2.16/0.67    spl4_34 <=> k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 2.16/0.67  fof(f56,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 2.16/0.67    inference(cnf_transformation,[],[f37])).
% 2.16/0.67  fof(f3498,plain,(
% 2.16/0.67    ~spl4_11 | spl4_33 | ~spl4_37),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f3497])).
% 2.16/0.67  fof(f3497,plain,(
% 2.16/0.67    $false | (~spl4_11 | spl4_33 | ~spl4_37)),
% 2.16/0.67    inference(subsumption_resolution,[],[f3472,f3438])).
% 2.16/0.67  fof(f3438,plain,(
% 2.16/0.67    ( ! [X17] : (r1_tarski(k2_zfmisc_1(sK0,X17),k1_xboole_0)) ) | (~spl4_11 | ~spl4_37)),
% 2.16/0.67    inference(resolution,[],[f3001,f54])).
% 2.16/0.67  fof(f54,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f35])).
% 2.16/0.67  fof(f3001,plain,(
% 2.16/0.67    ( ! [X1] : (m1_subset_1(k2_zfmisc_1(sK0,X1),k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_11 | ~spl4_37)),
% 2.16/0.67    inference(forward_demodulation,[],[f2988,f2954])).
% 2.16/0.67  fof(f2988,plain,(
% 2.16/0.67    ( ! [X1] : (m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1),k1_zfmisc_1(k1_xboole_0))) )),
% 2.16/0.67    inference(superposition,[],[f2026,f74])).
% 2.16/0.67  fof(f2026,plain,(
% 2.16/0.67    ( ! [X6,X7] : (m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X6),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f2017,f276])).
% 2.16/0.67  fof(f2017,plain,(
% 2.16/0.67    ( ! [X6,X7] : (~r1_tarski(k1_relat_1(k1_xboole_0),X7) | m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X6),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))) )),
% 2.16/0.67    inference(superposition,[],[f694,f985])).
% 2.16/0.67  fof(f985,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X0))) )),
% 2.16/0.67    inference(resolution,[],[f634,f290])).
% 2.16/0.67  fof(f290,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f287,f46])).
% 2.16/0.67  fof(f287,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) | ~v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.16/0.67    inference(resolution,[],[f217,f47])).
% 2.16/0.67  fof(f217,plain,(
% 2.16/0.67    ( ! [X8,X9] : (v4_relat_1(k2_zfmisc_1(X8,X9),X8)) )),
% 2.16/0.67    inference(resolution,[],[f120,f63])).
% 2.16/0.67  fof(f694,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X2) | m1_subset_1(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f688,f46])).
% 2.16/0.67  fof(f688,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (m1_subset_1(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X2) | ~v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.16/0.67    inference(resolution,[],[f294,f59])).
% 2.16/0.67  fof(f294,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f291,f46])).
% 2.16/0.67  fof(f291,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) | ~v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.16/0.67    inference(resolution,[],[f218,f49])).
% 2.16/0.67  fof(f218,plain,(
% 2.16/0.67    ( ! [X10,X11] : (v5_relat_1(k2_zfmisc_1(X10,X11),X11)) )),
% 2.16/0.67    inference(resolution,[],[f120,f64])).
% 2.16/0.67  fof(f3472,plain,(
% 2.16/0.67    ~r1_tarski(k2_zfmisc_1(sK0,sK0),k1_xboole_0) | (~spl4_11 | spl4_33 | ~spl4_37)),
% 2.16/0.67    inference(superposition,[],[f1916,f2954])).
% 2.16/0.67  fof(f1916,plain,(
% 2.16/0.67    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)),k1_xboole_0) | spl4_33),
% 2.16/0.67    inference(superposition,[],[f977,f986])).
% 2.16/0.67  fof(f977,plain,(
% 2.16/0.67    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)),k1_xboole_0) | spl4_33),
% 2.16/0.67    inference(avatar_component_clause,[],[f975])).
% 2.16/0.67  fof(f975,plain,(
% 2.16/0.67    spl4_33 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)),k1_xboole_0)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.16/0.67  fof(f1147,plain,(
% 2.16/0.67    spl4_2 | ~spl4_5 | ~spl4_10 | ~spl4_18),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f1146])).
% 2.16/0.67  fof(f1146,plain,(
% 2.16/0.67    $false | (spl4_2 | ~spl4_5 | ~spl4_10 | ~spl4_18)),
% 2.16/0.67    inference(subsumption_resolution,[],[f1109,f305])).
% 2.16/0.67  fof(f305,plain,(
% 2.16/0.67    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_18),
% 2.16/0.67    inference(avatar_component_clause,[],[f304])).
% 2.16/0.67  fof(f304,plain,(
% 2.16/0.67    spl4_18 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.16/0.67  fof(f1109,plain,(
% 2.16/0.67    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5 | ~spl4_10)),
% 2.16/0.67    inference(superposition,[],[f432,f1064])).
% 2.16/0.67  fof(f1064,plain,(
% 2.16/0.67    k1_xboole_0 = sK3 | (~spl4_5 | ~spl4_10)),
% 2.16/0.67    inference(subsumption_resolution,[],[f597,f997])).
% 2.16/0.67  fof(f997,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl4_5 | ~spl4_10)),
% 2.16/0.67    inference(forward_demodulation,[],[f996,f580])).
% 2.16/0.67  fof(f580,plain,(
% 2.16/0.67    k1_xboole_0 = k1_relat_1(sK3) | (~spl4_5 | ~spl4_10)),
% 2.16/0.67    inference(subsumption_resolution,[],[f539,f579])).
% 2.16/0.67  fof(f579,plain,(
% 2.16/0.67    r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | ~spl4_10)),
% 2.16/0.67    inference(forward_demodulation,[],[f171,f100])).
% 2.16/0.67  fof(f100,plain,(
% 2.16/0.67    k1_xboole_0 = sK0 | ~spl4_5),
% 2.16/0.67    inference(avatar_component_clause,[],[f98])).
% 2.16/0.67  fof(f171,plain,(
% 2.16/0.67    r1_tarski(sK0,k1_relat_1(sK3)) | ~spl4_10),
% 2.16/0.67    inference(avatar_component_clause,[],[f170])).
% 2.16/0.67  fof(f170,plain,(
% 2.16/0.67    spl4_10 <=> r1_tarski(sK0,k1_relat_1(sK3))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.16/0.67  fof(f539,plain,(
% 2.16/0.67    k1_xboole_0 = k1_relat_1(sK3) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | ~spl4_5),
% 2.16/0.67    inference(resolution,[],[f439,f53])).
% 2.16/0.67  fof(f439,plain,(
% 2.16/0.67    r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~spl4_5),
% 2.16/0.67    inference(superposition,[],[f143,f100])).
% 2.16/0.67  fof(f996,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(sK3),X0)) ) | ~spl4_5),
% 2.16/0.67    inference(subsumption_resolution,[],[f995,f122])).
% 2.16/0.67  fof(f995,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) ) | ~spl4_5),
% 2.16/0.67    inference(resolution,[],[f724,f47])).
% 2.16/0.67  fof(f724,plain,(
% 2.16/0.67    ( ! [X1] : (v4_relat_1(sK3,X1)) ) | ~spl4_5),
% 2.16/0.67    inference(resolution,[],[f542,f140])).
% 2.16/0.67  fof(f542,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 2.16/0.67    inference(forward_demodulation,[],[f541,f74])).
% 2.16/0.67  fof(f541,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))) | ~spl4_5),
% 2.16/0.67    inference(subsumption_resolution,[],[f537,f122])).
% 2.16/0.67  fof(f537,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))) | ~v1_relat_1(sK3) | ~spl4_5),
% 2.16/0.67    inference(resolution,[],[f439,f157])).
% 2.16/0.67  fof(f157,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 2.16/0.67    inference(resolution,[],[f59,f71])).
% 2.16/0.67  fof(f597,plain,(
% 2.16/0.67    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | ~spl4_5),
% 2.16/0.67    inference(resolution,[],[f452,f53])).
% 2.16/0.67  fof(f452,plain,(
% 2.16/0.67    r1_tarski(sK3,k1_xboole_0) | ~spl4_5),
% 2.16/0.67    inference(forward_demodulation,[],[f434,f74])).
% 2.16/0.67  fof(f434,plain,(
% 2.16/0.67    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_5),
% 2.16/0.67    inference(superposition,[],[f118,f100])).
% 2.16/0.67  fof(f118,plain,(
% 2.16/0.67    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 2.16/0.67    inference(resolution,[],[f54,f41])).
% 2.16/0.67  fof(f432,plain,(
% 2.16/0.67    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5)),
% 2.16/0.67    inference(superposition,[],[f87,f100])).
% 2.16/0.67  fof(f87,plain,(
% 2.16/0.67    ~v1_funct_2(sK3,sK0,sK2) | spl4_2),
% 2.16/0.67    inference(avatar_component_clause,[],[f85])).
% 2.16/0.67  fof(f85,plain,(
% 2.16/0.67    spl4_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.16/0.67  fof(f1058,plain,(
% 2.16/0.67    ~spl4_5 | ~spl4_10 | spl4_19),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f1057])).
% 2.16/0.67  fof(f1057,plain,(
% 2.16/0.67    $false | (~spl4_5 | ~spl4_10 | spl4_19)),
% 2.16/0.67    inference(subsumption_resolution,[],[f1056,f309])).
% 2.16/0.67  fof(f309,plain,(
% 2.16/0.67    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl4_19),
% 2.16/0.67    inference(avatar_component_clause,[],[f307])).
% 2.16/0.67  fof(f307,plain,(
% 2.16/0.67    spl4_19 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.16/0.67  fof(f1056,plain,(
% 2.16/0.67    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_5 | ~spl4_10)),
% 2.16/0.67    inference(forward_demodulation,[],[f1047,f74])).
% 2.16/0.67  fof(f1047,plain,(
% 2.16/0.67    ( ! [X2] : (k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X2))) ) | (~spl4_5 | ~spl4_10)),
% 2.16/0.67    inference(resolution,[],[f997,f681])).
% 2.16/0.67  fof(f681,plain,(
% 2.16/0.67    ( ! [X4,X5] : (~r1_tarski(X4,k1_relat_1(k2_zfmisc_1(X4,X5))) | k1_relat_1(k2_zfmisc_1(X4,X5)) = X4) )),
% 2.16/0.67    inference(resolution,[],[f290,f53])).
% 2.16/0.67  fof(f982,plain,(
% 2.16/0.67    ~spl4_33 | spl4_34),
% 2.16/0.67    inference(avatar_split_clause,[],[f972,f979,f975])).
% 2.16/0.67  fof(f972,plain,(
% 2.16/0.67    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)),k1_xboole_0)),
% 2.16/0.67    inference(resolution,[],[f705,f53])).
% 2.16/0.67  fof(f705,plain,(
% 2.16/0.67    r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))),
% 2.16/0.67    inference(resolution,[],[f317,f54])).
% 2.16/0.67  fof(f317,plain,(
% 2.16/0.67    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))))),
% 2.16/0.67    inference(resolution,[],[f257,f116])).
% 2.16/0.67  fof(f257,plain,(
% 2.16/0.67    ( ! [X0] : (~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 2.16/0.67    inference(resolution,[],[f157,f71])).
% 2.16/0.67  fof(f577,plain,(
% 2.16/0.67    spl4_2 | ~spl4_4 | ~spl4_5),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f574])).
% 2.16/0.67  fof(f574,plain,(
% 2.16/0.67    $false | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 2.16/0.67    inference(resolution,[],[f529,f432])).
% 2.16/0.67  fof(f529,plain,(
% 2.16/0.67    ( ! [X0] : (v1_funct_2(sK3,k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_5)),
% 2.16/0.67    inference(subsumption_resolution,[],[f524,f496])).
% 2.16/0.67  fof(f496,plain,(
% 2.16/0.67    k1_xboole_0 = k1_relat_1(sK3) | (~spl4_4 | ~spl4_5)),
% 2.16/0.67    inference(superposition,[],[f468,f414])).
% 2.16/0.67  fof(f414,plain,(
% 2.16/0.67    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5)),
% 2.16/0.67    inference(forward_demodulation,[],[f400,f100])).
% 2.16/0.67  fof(f400,plain,(
% 2.16/0.67    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl4_4),
% 2.16/0.67    inference(superposition,[],[f149,f95])).
% 2.16/0.67  fof(f95,plain,(
% 2.16/0.67    k1_xboole_0 = sK1 | ~spl4_4),
% 2.16/0.67    inference(avatar_component_clause,[],[f94])).
% 2.16/0.67  fof(f94,plain,(
% 2.16/0.67    spl4_4 <=> k1_xboole_0 = sK1),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.16/0.67  fof(f149,plain,(
% 2.16/0.67    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 2.16/0.67    inference(resolution,[],[f61,f41])).
% 2.16/0.67  fof(f468,plain,(
% 2.16/0.67    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5)),
% 2.16/0.67    inference(subsumption_resolution,[],[f463,f408])).
% 2.16/0.67  fof(f408,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_4),
% 2.16/0.67    inference(forward_demodulation,[],[f393,f73])).
% 2.16/0.67  fof(f393,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_4),
% 2.16/0.67    inference(superposition,[],[f41,f95])).
% 2.16/0.67  fof(f463,plain,(
% 2.16/0.67    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | ~spl4_5)),
% 2.16/0.67    inference(resolution,[],[f407,f113])).
% 2.16/0.67  fof(f113,plain,(
% 2.16/0.67    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 2.16/0.67    inference(forward_demodulation,[],[f79,f74])).
% 2.16/0.67  fof(f79,plain,(
% 2.16/0.67    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.16/0.67    inference(equality_resolution,[],[f66])).
% 2.16/0.67  fof(f66,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f38])).
% 2.16/0.67  fof(f407,plain,(
% 2.16/0.67    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 2.16/0.67    inference(forward_demodulation,[],[f392,f100])).
% 2.16/0.67  fof(f392,plain,(
% 2.16/0.67    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 2.16/0.67    inference(superposition,[],[f40,f95])).
% 2.16/0.67  fof(f40,plain,(
% 2.16/0.67    v1_funct_2(sK3,sK0,sK1)),
% 2.16/0.67    inference(cnf_transformation,[],[f30])).
% 2.16/0.67  fof(f524,plain,(
% 2.16/0.67    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3) | v1_funct_2(sK3,k1_xboole_0,X0)) ) | ~spl4_4),
% 2.16/0.67    inference(superposition,[],[f471,f477])).
% 2.16/0.67  fof(f477,plain,(
% 2.16/0.67    ( ! [X4] : (k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,X4,sK3)) ) | ~spl4_4),
% 2.16/0.67    inference(resolution,[],[f408,f151])).
% 2.16/0.67  fof(f151,plain,(
% 2.16/0.67    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 2.16/0.67    inference(superposition,[],[f61,f74])).
% 2.16/0.67  fof(f471,plain,(
% 2.16/0.67    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,sK3) | v1_funct_2(sK3,k1_xboole_0,X0)) ) | ~spl4_4),
% 2.16/0.67    inference(resolution,[],[f408,f112])).
% 2.16/0.67  fof(f112,plain,(
% 2.16/0.67    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 2.16/0.67    inference(forward_demodulation,[],[f78,f74])).
% 2.16/0.67  fof(f78,plain,(
% 2.16/0.67    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.16/0.67    inference(equality_resolution,[],[f68])).
% 2.16/0.67  fof(f68,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f38])).
% 2.16/0.67  fof(f571,plain,(
% 2.16/0.67    ~spl4_4 | ~spl4_5 | spl4_10),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f570])).
% 2.16/0.67  fof(f570,plain,(
% 2.16/0.67    $false | (~spl4_4 | ~spl4_5 | spl4_10)),
% 2.16/0.67    inference(subsumption_resolution,[],[f564,f71])).
% 2.16/0.67  fof(f564,plain,(
% 2.16/0.67    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5 | spl4_10)),
% 2.16/0.67    inference(superposition,[],[f423,f496])).
% 2.16/0.67  fof(f423,plain,(
% 2.16/0.67    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | spl4_10)),
% 2.16/0.67    inference(forward_demodulation,[],[f172,f100])).
% 2.16/0.67  fof(f172,plain,(
% 2.16/0.67    ~r1_tarski(sK0,k1_relat_1(sK3)) | spl4_10),
% 2.16/0.67    inference(avatar_component_clause,[],[f170])).
% 2.16/0.67  fof(f310,plain,(
% 2.16/0.67    spl4_18 | ~spl4_19),
% 2.16/0.67    inference(avatar_split_clause,[],[f301,f307,f304])).
% 2.16/0.67  fof(f301,plain,(
% 2.16/0.67    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 2.16/0.67    inference(superposition,[],[f221,f253])).
% 2.16/0.67  fof(f253,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 2.16/0.67    inference(resolution,[],[f151,f120])).
% 2.16/0.67  fof(f221,plain,(
% 2.16/0.67    ( ! [X16] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X16,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X16)) )),
% 2.16/0.67    inference(resolution,[],[f120,f112])).
% 2.16/0.67  fof(f283,plain,(
% 2.16/0.67    spl4_4 | spl4_10),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f282])).
% 2.16/0.67  fof(f282,plain,(
% 2.16/0.67    $false | (spl4_4 | spl4_10)),
% 2.16/0.67    inference(subsumption_resolution,[],[f281,f71])).
% 2.16/0.67  fof(f281,plain,(
% 2.16/0.67    ~r1_tarski(sK0,sK0) | (spl4_4 | spl4_10)),
% 2.16/0.67    inference(superposition,[],[f172,f202])).
% 2.16/0.67  fof(f202,plain,(
% 2.16/0.67    sK0 = k1_relat_1(sK3) | spl4_4),
% 2.16/0.67    inference(superposition,[],[f162,f149])).
% 2.16/0.67  fof(f162,plain,(
% 2.16/0.67    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 2.16/0.67    inference(subsumption_resolution,[],[f161,f96])).
% 2.16/0.67  fof(f96,plain,(
% 2.16/0.67    k1_xboole_0 != sK1 | spl4_4),
% 2.16/0.67    inference(avatar_component_clause,[],[f94])).
% 2.16/0.67  fof(f161,plain,(
% 2.16/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.16/0.67    inference(subsumption_resolution,[],[f158,f40])).
% 2.16/0.67  fof(f158,plain,(
% 2.16/0.67    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.16/0.67    inference(resolution,[],[f65,f41])).
% 2.16/0.67  fof(f65,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f38])).
% 2.16/0.67  fof(f206,plain,(
% 2.16/0.67    spl4_4 | spl4_11),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f205])).
% 2.16/0.67  fof(f205,plain,(
% 2.16/0.67    $false | (spl4_4 | spl4_11)),
% 2.16/0.67    inference(subsumption_resolution,[],[f202,f175])).
% 2.16/0.67  fof(f175,plain,(
% 2.16/0.67    sK0 != k1_relat_1(sK3) | spl4_11),
% 2.16/0.67    inference(avatar_component_clause,[],[f174])).
% 2.16/0.67  fof(f177,plain,(
% 2.16/0.67    ~spl4_10 | spl4_11),
% 2.16/0.67    inference(avatar_split_clause,[],[f167,f174,f170])).
% 2.16/0.67  fof(f167,plain,(
% 2.16/0.67    sK0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3))),
% 2.16/0.67    inference(resolution,[],[f143,f53])).
% 2.16/0.67  fof(f115,plain,(
% 2.16/0.67    spl4_1),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f114])).
% 2.16/0.67  fof(f114,plain,(
% 2.16/0.67    $false | spl4_1),
% 2.16/0.67    inference(subsumption_resolution,[],[f83,f39])).
% 2.16/0.67  fof(f83,plain,(
% 2.16/0.67    ~v1_funct_1(sK3) | spl4_1),
% 2.16/0.67    inference(avatar_component_clause,[],[f81])).
% 2.16/0.67  fof(f81,plain,(
% 2.16/0.67    spl4_1 <=> v1_funct_1(sK3)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.16/0.67  fof(f101,plain,(
% 2.16/0.67    ~spl4_4 | spl4_5),
% 2.16/0.67    inference(avatar_split_clause,[],[f43,f98,f94])).
% 2.16/0.67  fof(f43,plain,(
% 2.16/0.67    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.16/0.67    inference(cnf_transformation,[],[f30])).
% 2.16/0.67  fof(f92,plain,(
% 2.16/0.67    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 2.16/0.67    inference(avatar_split_clause,[],[f44,f89,f85,f81])).
% 2.16/0.67  % SZS output end Proof for theBenchmark
% 2.16/0.67  % (29376)------------------------------
% 2.16/0.67  % (29376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (29376)Termination reason: Refutation
% 2.16/0.67  
% 2.16/0.67  % (29376)Memory used [KB]: 12920
% 2.16/0.67  % (29376)Time elapsed: 0.231 s
% 2.16/0.67  % (29376)------------------------------
% 2.16/0.67  % (29376)------------------------------
% 2.16/0.68  % (29364)Success in time 0.31 s
%------------------------------------------------------------------------------
