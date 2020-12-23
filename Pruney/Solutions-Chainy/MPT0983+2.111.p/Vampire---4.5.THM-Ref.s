%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:50 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 667 expanded)
%              Number of leaves         :   38 ( 197 expanded)
%              Depth                    :   19
%              Number of atoms          :  680 (3033 expanded)
%              Number of equality atoms :   65 ( 140 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1926,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f585,f1201,f1226,f1242,f1320,f1417,f1695,f1759,f1809,f1925])).

fof(f1925,plain,
    ( ~ spl6_24
    | spl6_55 ),
    inference(avatar_contradiction_clause,[],[f1924])).

fof(f1924,plain,
    ( $false
    | ~ spl6_24
    | spl6_55 ),
    inference(subsumption_resolution,[],[f1923,f1764])).

fof(f1764,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK3))
    | spl6_55 ),
    inference(avatar_component_clause,[],[f1762])).

fof(f1762,plain,
    ( spl6_55
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f1923,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f1922,f117])).

fof(f117,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f82,f77])).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f82,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1922,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1921,f145])).

fof(f145,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f141,f89])).

fof(f89,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f141,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f84,f70])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1921,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1911,f146])).

fof(f146,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f142,f89])).

fof(f142,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f84,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f1911,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_24 ),
    inference(superposition,[],[f83,f1209])).

fof(f1209,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1207,plain,
    ( spl6_24
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1809,plain,
    ( ~ spl6_55
    | spl6_48
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f1803,f1639,f1629,f1762])).

fof(f1629,plain,
    ( spl6_48
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f1639,plain,
    ( spl6_50
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f1803,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl6_50 ),
    inference(resolution,[],[f1640,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1640,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f1639])).

fof(f1759,plain,
    ( spl6_2
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f1758])).

fof(f1758,plain,
    ( $false
    | spl6_2
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f1757,f146])).

fof(f1757,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_2
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f1744,f132])).

fof(f132,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1744,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_48 ),
    inference(superposition,[],[f317,f1631])).

fof(f1631,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f317,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f119,f223])).

fof(f223,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f92,f120])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f119,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f1695,plain,(
    spl6_50 ),
    inference(avatar_contradiction_clause,[],[f1694])).

fof(f1694,plain,
    ( $false
    | spl6_50 ),
    inference(subsumption_resolution,[],[f1693,f146])).

fof(f1693,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_50 ),
    inference(subsumption_resolution,[],[f1687,f303])).

fof(f303,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f106,f73])).

fof(f106,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1687,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl6_50 ),
    inference(resolution,[],[f1641,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1641,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_50 ),
    inference(avatar_component_clause,[],[f1639])).

fof(f1417,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f183,f152,f156])).

fof(f156,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f152,plain,
    ( spl6_3
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f183,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f150,f137])).

fof(f137,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f103,f70])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f150,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f85,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f1320,plain,
    ( spl6_1
    | spl6_3
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f1319])).

fof(f1319,plain,
    ( $false
    | spl6_1
    | spl6_3
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1280,f174])).

fof(f174,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f173,f120])).

fof(f173,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f90,f76])).

fof(f76,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f90,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f1280,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_1
    | spl6_3
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f169,f1254])).

fof(f1254,plain,
    ( k1_xboole_0 = sK0
    | spl6_1
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1253,f68])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f1253,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1252,f69])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f1252,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1251,f70])).

fof(f1251,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1250,f71])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f1250,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1249,f72])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f1249,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1248,f73])).

fof(f1248,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1247,f128])).

fof(f128,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1247,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1232,f115])).

fof(f115,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f80,f77])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1232,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_22 ),
    inference(superposition,[],[f107,f1200])).

fof(f1200,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f1198])).

fof(f1198,plain,
    ( spl6_22
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f107,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f169,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_3 ),
    inference(resolution,[],[f154,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f154,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1242,plain,
    ( spl6_24
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f1241,f1198,f1207])).

fof(f1241,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1240,f68])).

fof(f1240,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1239,f70])).

fof(f1239,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1238,f71])).

fof(f1238,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1230,f73])).

fof(f1230,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_22 ),
    inference(superposition,[],[f111,f1200])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f1226,plain,(
    spl6_21 ),
    inference(avatar_contradiction_clause,[],[f1225])).

fof(f1225,plain,
    ( $false
    | spl6_21 ),
    inference(subsumption_resolution,[],[f1224,f68])).

fof(f1224,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_21 ),
    inference(subsumption_resolution,[],[f1223,f70])).

fof(f1223,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_21 ),
    inference(subsumption_resolution,[],[f1222,f71])).

fof(f1222,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_21 ),
    inference(subsumption_resolution,[],[f1219,f73])).

fof(f1219,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_21 ),
    inference(resolution,[],[f1196,f113])).

fof(f113,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1196,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f1194])).

fof(f1194,plain,
    ( spl6_21
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1201,plain,
    ( ~ spl6_21
    | spl6_22 ),
    inference(avatar_split_clause,[],[f1187,f1198,f1194])).

fof(f1187,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f405,f74])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f405,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f109,f114])).

fof(f114,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f78,f77])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f585,plain,
    ( ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f582,f126,f156])).

fof(f582,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_1 ),
    inference(resolution,[],[f560,f128])).

fof(f560,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f537,f387])).

fof(f387,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f324,f320])).

fof(f320,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f319,f149])).

fof(f149,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X0))
      | v1_xboole_0(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f85,f114])).

fof(f319,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f318,f89])).

fof(f318,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_zfmisc_1(X0,k1_xboole_0))
      | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f313,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f313,plain,(
    ! [X0] : v1_xboole_0(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f312,f89])).

fof(f312,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_zfmisc_1(X0,k1_xboole_0))
      | v1_xboole_0(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(resolution,[],[f306,f217])).

fof(f217,plain,(
    ! [X0] :
      ( ~ v5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(resolution,[],[f91,f173])).

fof(f306,plain,(
    ! [X0,X1] : v5_relat_1(k2_zfmisc_1(X0,X1),X1) ),
    inference(resolution,[],[f305,f120])).

fof(f305,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X3,X2))
      | v5_relat_1(X1,X2) ) ),
    inference(resolution,[],[f106,f104])).

fof(f324,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(k6_partfun1(X1))
      | X1 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f314,f247])).

fof(f247,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f99,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f101,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f314,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f307,f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(k6_partfun1(X0),X1)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f220,f116])).

fof(f116,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f79,f77])).

fof(f79,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f220,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f91,f117])).

fof(f307,plain,(
    ! [X2,X3] :
      ( v5_relat_1(X2,X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f305,f185])).

fof(f537,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f115,f530])).

fof(f530,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f522,f319])).

fof(f522,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X4,X4))
      | k1_xboole_0 = k6_partfun1(X4) ) ),
    inference(resolution,[],[f466,f436])).

fof(f436,plain,(
    ! [X2,X1] :
      ( r1_tarski(k6_partfun1(X1),X2)
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ) ),
    inference(resolution,[],[f433,f101])).

fof(f433,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k6_partfun1(X1))
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ) ),
    inference(resolution,[],[f274,f87])).

fof(f274,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,k2_zfmisc_1(X9,X9))
      | ~ r2_hidden(X8,k6_partfun1(X9)) ) ),
    inference(resolution,[],[f100,f140])).

fof(f140,plain,(
    ! [X0] : r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f114,f103])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f466,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f462,f99])).

fof(f462,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(resolution,[],[f453,f319])).

fof(f453,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f443,f221])).

fof(f443,plain,(
    ! [X12,X13] :
      ( v5_relat_1(k6_partfun1(X12),X13)
      | ~ v1_xboole_0(k2_zfmisc_1(X12,X12)) ) ),
    inference(resolution,[],[f436,f305])).

fof(f133,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f75,f130,f126])).

fof(f75,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:33 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (28528)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (28536)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (28536)Refutation not found, incomplete strategy% (28536)------------------------------
% 0.21/0.51  % (28536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28536)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28536)Memory used [KB]: 11001
% 0.21/0.53  % (28536)Time elapsed: 0.070 s
% 0.21/0.53  % (28536)------------------------------
% 0.21/0.53  % (28536)------------------------------
% 0.21/0.54  % (28529)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.55  % (28514)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.55  % (28516)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.55  % (28537)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.56  % (28521)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.56  % (28517)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.56  % (28522)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.56  % (28543)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.56  % (28542)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.57  % (28520)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.57  % (28538)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.57  % (28541)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.57  % (28518)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.49/0.57  % (28540)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.57  % (28530)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.57  % (28533)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.57  % (28524)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.49/0.57  % (28527)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.57  % (28526)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.58  % (28525)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.58  % (28539)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.58  % (28535)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.58  % (28534)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.58  % (28532)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.59  % (28523)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.59  % (28544)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.49/0.59  % (28531)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.60  % (28519)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.49/0.61  % (28515)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.27/0.68  % (28541)Refutation found. Thanks to Tanya!
% 2.27/0.68  % SZS status Theorem for theBenchmark
% 2.27/0.68  % SZS output start Proof for theBenchmark
% 2.27/0.68  fof(f1926,plain,(
% 2.27/0.68    $false),
% 2.27/0.68    inference(avatar_sat_refutation,[],[f133,f585,f1201,f1226,f1242,f1320,f1417,f1695,f1759,f1809,f1925])).
% 2.27/0.68  fof(f1925,plain,(
% 2.27/0.68    ~spl6_24 | spl6_55),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1924])).
% 2.27/0.68  fof(f1924,plain,(
% 2.27/0.68    $false | (~spl6_24 | spl6_55)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1923,f1764])).
% 2.27/0.68  fof(f1764,plain,(
% 2.27/0.68    ~r1_tarski(sK0,k2_relat_1(sK3)) | spl6_55),
% 2.27/0.68    inference(avatar_component_clause,[],[f1762])).
% 2.27/0.68  fof(f1762,plain,(
% 2.27/0.68    spl6_55 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 2.27/0.68  fof(f1923,plain,(
% 2.27/0.68    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl6_24),
% 2.27/0.68    inference(forward_demodulation,[],[f1922,f117])).
% 2.27/0.68  fof(f117,plain,(
% 2.27/0.68    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.27/0.68    inference(definition_unfolding,[],[f82,f77])).
% 2.27/0.68  fof(f77,plain,(
% 2.27/0.68    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f23])).
% 2.27/0.68  fof(f23,axiom,(
% 2.27/0.68    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.27/0.68  fof(f82,plain,(
% 2.27/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.27/0.68    inference(cnf_transformation,[],[f15])).
% 2.27/0.68  fof(f15,axiom,(
% 2.27/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.27/0.68  fof(f1922,plain,(
% 2.27/0.68    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~spl6_24),
% 2.27/0.68    inference(subsumption_resolution,[],[f1921,f145])).
% 2.27/0.68  fof(f145,plain,(
% 2.27/0.68    v1_relat_1(sK2)),
% 2.27/0.68    inference(subsumption_resolution,[],[f141,f89])).
% 2.27/0.68  fof(f89,plain,(
% 2.27/0.68    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.27/0.68    inference(cnf_transformation,[],[f12])).
% 2.27/0.68  fof(f12,axiom,(
% 2.27/0.68    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.27/0.68  fof(f141,plain,(
% 2.27/0.68    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.27/0.68    inference(resolution,[],[f84,f70])).
% 2.27/0.68  fof(f70,plain,(
% 2.27/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.27/0.68    inference(cnf_transformation,[],[f53])).
% 2.27/0.68  fof(f53,plain,(
% 2.27/0.68    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.27/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f52,f51])).
% 2.27/0.68  fof(f51,plain,(
% 2.27/0.68    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.27/0.68    introduced(choice_axiom,[])).
% 2.27/0.68  fof(f52,plain,(
% 2.27/0.68    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.27/0.68    introduced(choice_axiom,[])).
% 2.27/0.68  fof(f28,plain,(
% 2.27/0.68    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.27/0.68    inference(flattening,[],[f27])).
% 2.27/0.68  fof(f27,plain,(
% 2.27/0.68    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.27/0.68    inference(ennf_transformation,[],[f26])).
% 2.27/0.68  fof(f26,negated_conjecture,(
% 2.27/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.27/0.68    inference(negated_conjecture,[],[f25])).
% 2.27/0.68  fof(f25,conjecture,(
% 2.27/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 2.27/0.68  fof(f84,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f30])).
% 2.27/0.68  fof(f30,plain,(
% 2.27/0.68    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.27/0.68    inference(ennf_transformation,[],[f10])).
% 2.27/0.68  fof(f10,axiom,(
% 2.27/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.27/0.68  fof(f1921,plain,(
% 2.27/0.68    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK2) | ~spl6_24),
% 2.27/0.68    inference(subsumption_resolution,[],[f1911,f146])).
% 2.27/0.68  fof(f146,plain,(
% 2.27/0.68    v1_relat_1(sK3)),
% 2.27/0.68    inference(subsumption_resolution,[],[f142,f89])).
% 2.27/0.68  fof(f142,plain,(
% 2.27/0.68    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.27/0.68    inference(resolution,[],[f84,f73])).
% 2.27/0.68  fof(f73,plain,(
% 2.27/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.27/0.68    inference(cnf_transformation,[],[f53])).
% 2.27/0.68  fof(f1911,plain,(
% 2.27/0.68    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_24),
% 2.27/0.68    inference(superposition,[],[f83,f1209])).
% 2.27/0.68  fof(f1209,plain,(
% 2.27/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl6_24),
% 2.27/0.68    inference(avatar_component_clause,[],[f1207])).
% 2.27/0.68  fof(f1207,plain,(
% 2.27/0.68    spl6_24 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.27/0.68  fof(f83,plain,(
% 2.27/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f29])).
% 2.27/0.68  fof(f29,plain,(
% 2.27/0.68    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.27/0.68    inference(ennf_transformation,[],[f14])).
% 2.27/0.68  fof(f14,axiom,(
% 2.27/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 2.27/0.68  fof(f1809,plain,(
% 2.27/0.68    ~spl6_55 | spl6_48 | ~spl6_50),
% 2.27/0.68    inference(avatar_split_clause,[],[f1803,f1639,f1629,f1762])).
% 2.27/0.68  fof(f1629,plain,(
% 2.27/0.68    spl6_48 <=> sK0 = k2_relat_1(sK3)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 2.27/0.68  fof(f1639,plain,(
% 2.27/0.68    spl6_50 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 2.27/0.68  fof(f1803,plain,(
% 2.27/0.68    sK0 = k2_relat_1(sK3) | ~r1_tarski(sK0,k2_relat_1(sK3)) | ~spl6_50),
% 2.27/0.68    inference(resolution,[],[f1640,f99])).
% 2.27/0.68  fof(f99,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f61])).
% 2.27/0.68  fof(f61,plain,(
% 2.27/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.27/0.68    inference(flattening,[],[f60])).
% 2.27/0.68  fof(f60,plain,(
% 2.27/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.27/0.68    inference(nnf_transformation,[],[f3])).
% 2.27/0.68  fof(f3,axiom,(
% 2.27/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.27/0.68  fof(f1640,plain,(
% 2.27/0.68    r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_50),
% 2.27/0.68    inference(avatar_component_clause,[],[f1639])).
% 2.27/0.68  fof(f1759,plain,(
% 2.27/0.68    spl6_2 | ~spl6_48),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1758])).
% 2.27/0.68  fof(f1758,plain,(
% 2.27/0.68    $false | (spl6_2 | ~spl6_48)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1757,f146])).
% 2.27/0.68  fof(f1757,plain,(
% 2.27/0.68    ~v1_relat_1(sK3) | (spl6_2 | ~spl6_48)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1744,f132])).
% 2.27/0.68  fof(f132,plain,(
% 2.27/0.68    ~v2_funct_2(sK3,sK0) | spl6_2),
% 2.27/0.68    inference(avatar_component_clause,[],[f130])).
% 2.27/0.68  fof(f130,plain,(
% 2.27/0.68    spl6_2 <=> v2_funct_2(sK3,sK0)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.27/0.68  fof(f1744,plain,(
% 2.27/0.68    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl6_48),
% 2.27/0.68    inference(superposition,[],[f317,f1631])).
% 2.27/0.68  fof(f1631,plain,(
% 2.27/0.68    sK0 = k2_relat_1(sK3) | ~spl6_48),
% 2.27/0.68    inference(avatar_component_clause,[],[f1629])).
% 2.27/0.68  fof(f317,plain,(
% 2.27/0.68    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.27/0.68    inference(subsumption_resolution,[],[f119,f223])).
% 2.27/0.68  fof(f223,plain,(
% 2.27/0.68    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.27/0.68    inference(resolution,[],[f92,f120])).
% 2.27/0.68  fof(f120,plain,(
% 2.27/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.27/0.68    inference(equality_resolution,[],[f98])).
% 2.27/0.68  fof(f98,plain,(
% 2.27/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.27/0.68    inference(cnf_transformation,[],[f61])).
% 2.27/0.68  fof(f92,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f58])).
% 2.27/0.68  fof(f58,plain,(
% 2.27/0.68    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.27/0.68    inference(nnf_transformation,[],[f36])).
% 2.27/0.68  fof(f36,plain,(
% 2.27/0.68    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.27/0.68    inference(ennf_transformation,[],[f11])).
% 2.27/0.68  fof(f11,axiom,(
% 2.27/0.68    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.27/0.68  fof(f119,plain,(
% 2.27/0.68    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.27/0.68    inference(equality_resolution,[],[f96])).
% 2.27/0.68  fof(f96,plain,(
% 2.27/0.68    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f59])).
% 2.27/0.68  fof(f59,plain,(
% 2.27/0.68    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.27/0.68    inference(nnf_transformation,[],[f40])).
% 2.27/0.68  fof(f40,plain,(
% 2.27/0.68    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.27/0.68    inference(flattening,[],[f39])).
% 2.27/0.68  fof(f39,plain,(
% 2.27/0.68    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.27/0.68    inference(ennf_transformation,[],[f20])).
% 2.27/0.68  fof(f20,axiom,(
% 2.27/0.68    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 2.27/0.68  fof(f1695,plain,(
% 2.27/0.68    spl6_50),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1694])).
% 2.27/0.68  fof(f1694,plain,(
% 2.27/0.68    $false | spl6_50),
% 2.27/0.68    inference(subsumption_resolution,[],[f1693,f146])).
% 2.27/0.68  fof(f1693,plain,(
% 2.27/0.68    ~v1_relat_1(sK3) | spl6_50),
% 2.27/0.68    inference(subsumption_resolution,[],[f1687,f303])).
% 2.27/0.68  fof(f303,plain,(
% 2.27/0.68    v5_relat_1(sK3,sK0)),
% 2.27/0.68    inference(resolution,[],[f106,f73])).
% 2.27/0.68  fof(f106,plain,(
% 2.27/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f42])).
% 2.27/0.68  fof(f42,plain,(
% 2.27/0.68    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.68    inference(ennf_transformation,[],[f17])).
% 2.27/0.68  fof(f17,axiom,(
% 2.27/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.27/0.68  fof(f1687,plain,(
% 2.27/0.68    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl6_50),
% 2.27/0.68    inference(resolution,[],[f1641,f91])).
% 2.27/0.68  fof(f91,plain,(
% 2.27/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f58])).
% 2.27/0.68  fof(f1641,plain,(
% 2.27/0.68    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_50),
% 2.27/0.68    inference(avatar_component_clause,[],[f1639])).
% 2.27/0.68  fof(f1417,plain,(
% 2.27/0.68    spl6_4 | ~spl6_3),
% 2.27/0.68    inference(avatar_split_clause,[],[f183,f152,f156])).
% 2.27/0.68  fof(f156,plain,(
% 2.27/0.68    spl6_4 <=> v1_xboole_0(sK2)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.27/0.68  fof(f152,plain,(
% 2.27/0.68    spl6_3 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.27/0.68  fof(f183,plain,(
% 2.27/0.68    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2)),
% 2.27/0.68    inference(resolution,[],[f150,f137])).
% 2.27/0.68  fof(f137,plain,(
% 2.27/0.68    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 2.27/0.68    inference(resolution,[],[f103,f70])).
% 2.27/0.68  fof(f103,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f66])).
% 2.27/0.68  fof(f66,plain,(
% 2.27/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.27/0.68    inference(nnf_transformation,[],[f9])).
% 2.27/0.68  fof(f9,axiom,(
% 2.27/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.27/0.68  fof(f150,plain,(
% 2.27/0.68    ( ! [X2,X1] : (~r1_tarski(X1,X2) | ~v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 2.27/0.68    inference(resolution,[],[f85,f104])).
% 2.27/0.68  fof(f104,plain,(
% 2.27/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f66])).
% 2.27/0.68  fof(f85,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f31])).
% 2.27/0.68  fof(f31,plain,(
% 2.27/0.68    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.27/0.68    inference(ennf_transformation,[],[f8])).
% 2.27/0.68  fof(f8,axiom,(
% 2.27/0.68    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 2.27/0.68  fof(f1320,plain,(
% 2.27/0.68    spl6_1 | spl6_3 | ~spl6_22),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1319])).
% 2.27/0.68  fof(f1319,plain,(
% 2.27/0.68    $false | (spl6_1 | spl6_3 | ~spl6_22)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1280,f174])).
% 2.27/0.68  fof(f174,plain,(
% 2.27/0.68    v1_xboole_0(k1_xboole_0)),
% 2.27/0.68    inference(resolution,[],[f173,f120])).
% 2.27/0.68  fof(f173,plain,(
% 2.27/0.68    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 2.27/0.68    inference(resolution,[],[f90,f76])).
% 2.27/0.68  fof(f76,plain,(
% 2.27/0.68    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f4])).
% 2.27/0.68  fof(f4,axiom,(
% 2.27/0.68    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.27/0.68  fof(f90,plain,(
% 2.27/0.68    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f35])).
% 2.27/0.68  fof(f35,plain,(
% 2.27/0.68    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.27/0.68    inference(flattening,[],[f34])).
% 2.27/0.68  fof(f34,plain,(
% 2.27/0.68    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.27/0.68    inference(ennf_transformation,[],[f5])).
% 2.27/0.68  fof(f5,axiom,(
% 2.27/0.68    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.27/0.68  fof(f1280,plain,(
% 2.27/0.68    ~v1_xboole_0(k1_xboole_0) | (spl6_1 | spl6_3 | ~spl6_22)),
% 2.27/0.68    inference(backward_demodulation,[],[f169,f1254])).
% 2.27/0.68  fof(f1254,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | (spl6_1 | ~spl6_22)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1253,f68])).
% 2.27/0.68  fof(f68,plain,(
% 2.27/0.68    v1_funct_1(sK2)),
% 2.27/0.68    inference(cnf_transformation,[],[f53])).
% 2.27/0.68  fof(f1253,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | (spl6_1 | ~spl6_22)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1252,f69])).
% 2.27/0.68  fof(f69,plain,(
% 2.27/0.68    v1_funct_2(sK2,sK0,sK1)),
% 2.27/0.68    inference(cnf_transformation,[],[f53])).
% 2.27/0.68  fof(f1252,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl6_1 | ~spl6_22)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1251,f70])).
% 2.27/0.68  fof(f1251,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl6_1 | ~spl6_22)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1250,f71])).
% 2.27/0.68  fof(f71,plain,(
% 2.27/0.68    v1_funct_1(sK3)),
% 2.27/0.68    inference(cnf_transformation,[],[f53])).
% 2.27/0.68  fof(f1250,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl6_1 | ~spl6_22)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1249,f72])).
% 2.27/0.68  fof(f72,plain,(
% 2.27/0.68    v1_funct_2(sK3,sK1,sK0)),
% 2.27/0.68    inference(cnf_transformation,[],[f53])).
% 2.27/0.68  fof(f1249,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl6_1 | ~spl6_22)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1248,f73])).
% 2.27/0.68  fof(f1248,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl6_1 | ~spl6_22)),
% 2.27/0.68    inference(subsumption_resolution,[],[f1247,f128])).
% 2.27/0.68  fof(f128,plain,(
% 2.27/0.68    ~v2_funct_1(sK2) | spl6_1),
% 2.27/0.68    inference(avatar_component_clause,[],[f126])).
% 2.27/0.68  fof(f126,plain,(
% 2.27/0.68    spl6_1 <=> v2_funct_1(sK2)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.27/0.68  fof(f1247,plain,(
% 2.27/0.68    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl6_22),
% 2.27/0.68    inference(subsumption_resolution,[],[f1232,f115])).
% 2.27/0.68  fof(f115,plain,(
% 2.27/0.68    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.27/0.68    inference(definition_unfolding,[],[f80,f77])).
% 2.27/0.68  fof(f80,plain,(
% 2.27/0.68    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.27/0.68    inference(cnf_transformation,[],[f16])).
% 2.27/0.68  fof(f16,axiom,(
% 2.27/0.68    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.27/0.68  fof(f1232,plain,(
% 2.27/0.68    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl6_22),
% 2.27/0.68    inference(superposition,[],[f107,f1200])).
% 2.27/0.68  fof(f1200,plain,(
% 2.27/0.68    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl6_22),
% 2.27/0.68    inference(avatar_component_clause,[],[f1198])).
% 2.27/0.68  fof(f1198,plain,(
% 2.27/0.68    spl6_22 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 2.27/0.68  fof(f107,plain,(
% 2.27/0.68    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f44])).
% 2.27/0.68  fof(f44,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.27/0.68    inference(flattening,[],[f43])).
% 2.27/0.68  fof(f43,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.27/0.68    inference(ennf_transformation,[],[f24])).
% 2.27/0.68  fof(f24,axiom,(
% 2.27/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 2.27/0.68  fof(f169,plain,(
% 2.27/0.68    ~v1_xboole_0(sK0) | spl6_3),
% 2.27/0.68    inference(resolution,[],[f154,f94])).
% 2.27/0.68  fof(f94,plain,(
% 2.27/0.68    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f38])).
% 2.27/0.68  fof(f38,plain,(
% 2.27/0.68    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.27/0.68    inference(ennf_transformation,[],[f7])).
% 2.27/0.68  fof(f7,axiom,(
% 2.27/0.68    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 2.27/0.68  fof(f154,plain,(
% 2.27/0.68    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl6_3),
% 2.27/0.68    inference(avatar_component_clause,[],[f152])).
% 2.27/0.68  fof(f1242,plain,(
% 2.27/0.68    spl6_24 | ~spl6_22),
% 2.27/0.68    inference(avatar_split_clause,[],[f1241,f1198,f1207])).
% 2.27/0.68  fof(f1241,plain,(
% 2.27/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl6_22),
% 2.27/0.68    inference(subsumption_resolution,[],[f1240,f68])).
% 2.27/0.68  fof(f1240,plain,(
% 2.27/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | ~spl6_22),
% 2.27/0.68    inference(subsumption_resolution,[],[f1239,f70])).
% 2.27/0.68  fof(f1239,plain,(
% 2.27/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl6_22),
% 2.27/0.68    inference(subsumption_resolution,[],[f1238,f71])).
% 2.27/0.68  fof(f1238,plain,(
% 2.27/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl6_22),
% 2.27/0.68    inference(subsumption_resolution,[],[f1230,f73])).
% 2.27/0.68  fof(f1230,plain,(
% 2.27/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl6_22),
% 2.27/0.68    inference(superposition,[],[f111,f1200])).
% 2.27/0.68  fof(f111,plain,(
% 2.27/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f48])).
% 2.27/0.68  fof(f48,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.27/0.68    inference(flattening,[],[f47])).
% 2.27/0.68  fof(f47,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.27/0.68    inference(ennf_transformation,[],[f22])).
% 2.27/0.68  fof(f22,axiom,(
% 2.27/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.27/0.68  fof(f1226,plain,(
% 2.27/0.68    spl6_21),
% 2.27/0.68    inference(avatar_contradiction_clause,[],[f1225])).
% 2.27/0.68  fof(f1225,plain,(
% 2.27/0.68    $false | spl6_21),
% 2.27/0.68    inference(subsumption_resolution,[],[f1224,f68])).
% 2.27/0.68  fof(f1224,plain,(
% 2.27/0.68    ~v1_funct_1(sK2) | spl6_21),
% 2.27/0.68    inference(subsumption_resolution,[],[f1223,f70])).
% 2.27/0.68  fof(f1223,plain,(
% 2.27/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_21),
% 2.27/0.68    inference(subsumption_resolution,[],[f1222,f71])).
% 2.27/0.68  fof(f1222,plain,(
% 2.27/0.68    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_21),
% 2.27/0.68    inference(subsumption_resolution,[],[f1219,f73])).
% 2.27/0.68  fof(f1219,plain,(
% 2.27/0.68    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_21),
% 2.27/0.68    inference(resolution,[],[f1196,f113])).
% 2.27/0.68  fof(f113,plain,(
% 2.27/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.27/0.68    inference(cnf_transformation,[],[f50])).
% 2.27/0.68  fof(f50,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.27/0.68    inference(flattening,[],[f49])).
% 2.27/0.68  fof(f49,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.27/0.68    inference(ennf_transformation,[],[f21])).
% 2.27/0.68  fof(f21,axiom,(
% 2.27/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.27/0.68  fof(f1196,plain,(
% 2.27/0.68    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_21),
% 2.27/0.68    inference(avatar_component_clause,[],[f1194])).
% 2.27/0.68  fof(f1194,plain,(
% 2.27/0.68    spl6_21 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.27/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.27/0.68  fof(f1201,plain,(
% 2.27/0.68    ~spl6_21 | spl6_22),
% 2.27/0.68    inference(avatar_split_clause,[],[f1187,f1198,f1194])).
% 2.27/0.68  fof(f1187,plain,(
% 2.27/0.68    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.27/0.68    inference(resolution,[],[f405,f74])).
% 2.27/0.68  fof(f74,plain,(
% 2.27/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.27/0.68    inference(cnf_transformation,[],[f53])).
% 2.27/0.68  fof(f405,plain,(
% 2.27/0.68    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.27/0.68    inference(resolution,[],[f109,f114])).
% 2.27/0.68  fof(f114,plain,(
% 2.27/0.68    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.27/0.68    inference(definition_unfolding,[],[f78,f77])).
% 2.27/0.68  fof(f78,plain,(
% 2.27/0.68    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.27/0.68    inference(cnf_transformation,[],[f19])).
% 2.27/0.68  fof(f19,axiom,(
% 2.27/0.68    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.27/0.68  fof(f109,plain,(
% 2.27/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.68    inference(cnf_transformation,[],[f67])).
% 2.27/0.68  fof(f67,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.68    inference(nnf_transformation,[],[f46])).
% 2.27/0.68  fof(f46,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.68    inference(flattening,[],[f45])).
% 2.27/0.68  fof(f45,plain,(
% 2.27/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.27/0.68    inference(ennf_transformation,[],[f18])).
% 2.27/0.68  fof(f18,axiom,(
% 2.27/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.27/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.27/0.68  fof(f585,plain,(
% 2.27/0.68    ~spl6_4 | spl6_1),
% 2.27/0.68    inference(avatar_split_clause,[],[f582,f126,f156])).
% 2.27/0.68  fof(f582,plain,(
% 2.27/0.68    ~v1_xboole_0(sK2) | spl6_1),
% 2.27/0.68    inference(resolution,[],[f560,f128])).
% 2.27/0.70  fof(f560,plain,(
% 2.27/0.70    ( ! [X0] : (v2_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.27/0.70    inference(superposition,[],[f537,f387])).
% 2.27/0.70  fof(f387,plain,(
% 2.27/0.70    ( ! [X2] : (k1_xboole_0 = X2 | ~v1_xboole_0(X2)) )),
% 2.27/0.70    inference(resolution,[],[f324,f320])).
% 2.27/0.70  fof(f320,plain,(
% 2.27/0.70    v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 2.27/0.70    inference(resolution,[],[f319,f149])).
% 2.27/0.70  fof(f149,plain,(
% 2.27/0.70    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(X0,X0)) | v1_xboole_0(k6_partfun1(X0))) )),
% 2.27/0.70    inference(resolution,[],[f85,f114])).
% 2.27/0.70  fof(f319,plain,(
% 2.27/0.70    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f318,f89])).
% 2.27/0.70  fof(f318,plain,(
% 2.27/0.70    ( ! [X0] : (~v1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 2.27/0.70    inference(resolution,[],[f313,f86])).
% 2.27/0.70  fof(f86,plain,(
% 2.27/0.70    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f33])).
% 2.27/0.70  fof(f33,plain,(
% 2.27/0.70    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.27/0.70    inference(flattening,[],[f32])).
% 2.27/0.70  fof(f32,plain,(
% 2.27/0.70    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f13])).
% 2.27/0.70  fof(f13,axiom,(
% 2.27/0.70    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 2.27/0.70  fof(f313,plain,(
% 2.27/0.70    ( ! [X0] : (v1_xboole_0(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f312,f89])).
% 2.27/0.70  fof(f312,plain,(
% 2.27/0.70    ( ! [X0] : (~v1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.27/0.70    inference(resolution,[],[f306,f217])).
% 2.27/0.70  fof(f217,plain,(
% 2.27/0.70    ( ! [X0] : (~v5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | v1_xboole_0(k2_relat_1(X0))) )),
% 2.27/0.70    inference(resolution,[],[f91,f173])).
% 2.27/0.70  fof(f306,plain,(
% 2.27/0.70    ( ! [X0,X1] : (v5_relat_1(k2_zfmisc_1(X0,X1),X1)) )),
% 2.27/0.70    inference(resolution,[],[f305,f120])).
% 2.27/0.70  fof(f305,plain,(
% 2.27/0.70    ( ! [X2,X3,X1] : (~r1_tarski(X1,k2_zfmisc_1(X3,X2)) | v5_relat_1(X1,X2)) )),
% 2.27/0.70    inference(resolution,[],[f106,f104])).
% 2.27/0.70  fof(f324,plain,(
% 2.27/0.70    ( ! [X2,X1] : (~v1_xboole_0(k6_partfun1(X1)) | X1 = X2 | ~v1_xboole_0(X2)) )),
% 2.27/0.70    inference(resolution,[],[f314,f247])).
% 2.27/0.70  fof(f247,plain,(
% 2.27/0.70    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~v1_xboole_0(X2)) )),
% 2.27/0.70    inference(resolution,[],[f99,f185])).
% 2.27/0.70  fof(f185,plain,(
% 2.27/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.27/0.70    inference(resolution,[],[f101,f87])).
% 2.27/0.70  fof(f87,plain,(
% 2.27/0.70    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f57])).
% 2.27/0.70  fof(f57,plain,(
% 2.27/0.70    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.27/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 2.27/0.70  fof(f56,plain,(
% 2.27/0.70    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.27/0.70    introduced(choice_axiom,[])).
% 2.27/0.70  fof(f55,plain,(
% 2.27/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.27/0.70    inference(rectify,[],[f54])).
% 2.27/0.70  fof(f54,plain,(
% 2.27/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.27/0.70    inference(nnf_transformation,[],[f1])).
% 2.27/0.70  fof(f1,axiom,(
% 2.27/0.70    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.27/0.70  fof(f101,plain,(
% 2.27/0.70    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f65])).
% 2.27/0.70  fof(f65,plain,(
% 2.27/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.27/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).
% 2.27/0.70  fof(f64,plain,(
% 2.27/0.70    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.27/0.70    introduced(choice_axiom,[])).
% 2.27/0.70  fof(f63,plain,(
% 2.27/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.27/0.70    inference(rectify,[],[f62])).
% 2.27/0.70  fof(f62,plain,(
% 2.27/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.27/0.70    inference(nnf_transformation,[],[f41])).
% 2.27/0.70  fof(f41,plain,(
% 2.27/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f2])).
% 2.27/0.70  fof(f2,axiom,(
% 2.27/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.27/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.27/0.70  fof(f314,plain,(
% 2.27/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(k6_partfun1(X0))) )),
% 2.27/0.70    inference(resolution,[],[f307,f221])).
% 2.27/0.70  fof(f221,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~v5_relat_1(k6_partfun1(X0),X1) | r1_tarski(X0,X1)) )),
% 2.27/0.70    inference(subsumption_resolution,[],[f220,f116])).
% 2.27/0.70  fof(f116,plain,(
% 2.27/0.70    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.27/0.70    inference(definition_unfolding,[],[f79,f77])).
% 2.27/0.70  fof(f79,plain,(
% 2.27/0.70    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f16])).
% 2.27/0.70  fof(f220,plain,(
% 2.27/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 2.27/0.70    inference(superposition,[],[f91,f117])).
% 2.27/0.70  fof(f307,plain,(
% 2.27/0.70    ( ! [X2,X3] : (v5_relat_1(X2,X3) | ~v1_xboole_0(X2)) )),
% 2.27/0.70    inference(resolution,[],[f305,f185])).
% 2.27/0.70  fof(f537,plain,(
% 2.27/0.70    v2_funct_1(k1_xboole_0)),
% 2.27/0.70    inference(superposition,[],[f115,f530])).
% 2.27/0.70  fof(f530,plain,(
% 2.27/0.70    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.27/0.70    inference(resolution,[],[f522,f319])).
% 2.27/0.70  fof(f522,plain,(
% 2.27/0.70    ( ! [X4] : (~v1_xboole_0(k2_zfmisc_1(X4,X4)) | k1_xboole_0 = k6_partfun1(X4)) )),
% 2.27/0.70    inference(resolution,[],[f466,f436])).
% 2.27/0.70  fof(f436,plain,(
% 2.27/0.70    ( ! [X2,X1] : (r1_tarski(k6_partfun1(X1),X2) | ~v1_xboole_0(k2_zfmisc_1(X1,X1))) )),
% 2.27/0.70    inference(resolution,[],[f433,f101])).
% 2.27/0.70  fof(f433,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~r2_hidden(X0,k6_partfun1(X1)) | ~v1_xboole_0(k2_zfmisc_1(X1,X1))) )),
% 2.27/0.70    inference(resolution,[],[f274,f87])).
% 2.27/0.70  fof(f274,plain,(
% 2.27/0.70    ( ! [X8,X9] : (r2_hidden(X8,k2_zfmisc_1(X9,X9)) | ~r2_hidden(X8,k6_partfun1(X9))) )),
% 2.27/0.70    inference(resolution,[],[f100,f140])).
% 2.27/0.70  fof(f140,plain,(
% 2.27/0.70    ( ! [X0] : (r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0))) )),
% 2.27/0.70    inference(resolution,[],[f114,f103])).
% 2.27/0.70  fof(f100,plain,(
% 2.27/0.70    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f65])).
% 2.27/0.70  fof(f466,plain,(
% 2.27/0.70    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 2.27/0.70    inference(resolution,[],[f462,f99])).
% 2.27/0.70  fof(f462,plain,(
% 2.27/0.70    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 2.27/0.70    inference(resolution,[],[f453,f319])).
% 2.27/0.70  fof(f453,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X0)) | r1_tarski(X0,X1)) )),
% 2.27/0.70    inference(resolution,[],[f443,f221])).
% 2.27/0.70  fof(f443,plain,(
% 2.27/0.70    ( ! [X12,X13] : (v5_relat_1(k6_partfun1(X12),X13) | ~v1_xboole_0(k2_zfmisc_1(X12,X12))) )),
% 2.27/0.70    inference(resolution,[],[f436,f305])).
% 2.27/0.70  fof(f133,plain,(
% 2.27/0.70    ~spl6_1 | ~spl6_2),
% 2.27/0.70    inference(avatar_split_clause,[],[f75,f130,f126])).
% 2.27/0.70  fof(f75,plain,(
% 2.27/0.70    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.27/0.70    inference(cnf_transformation,[],[f53])).
% 2.27/0.70  % SZS output end Proof for theBenchmark
% 2.27/0.70  % (28541)------------------------------
% 2.27/0.70  % (28541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.70  % (28541)Termination reason: Refutation
% 2.27/0.70  
% 2.27/0.70  % (28541)Memory used [KB]: 6908
% 2.27/0.70  % (28541)Time elapsed: 0.270 s
% 2.27/0.70  % (28541)------------------------------
% 2.27/0.70  % (28541)------------------------------
% 2.27/0.70  % (28513)Success in time 0.331 s
%------------------------------------------------------------------------------
