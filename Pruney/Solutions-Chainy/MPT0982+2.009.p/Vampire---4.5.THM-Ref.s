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
% DateTime   : Thu Dec  3 13:01:27 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 666 expanded)
%              Number of leaves         :   27 ( 213 expanded)
%              Depth                    :   22
%              Number of atoms          :  580 (5222 expanded)
%              Number of equality atoms :  146 (1603 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f738,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f120,f132,f144,f149,f178,f210,f497,f737])).

fof(f737,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f735,f223])).

fof(f223,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f61,f152])).

fof(f152,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f54,f80])).

% (24107)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK3)
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK1 != k2_relset_1(sK0,sK1,sK3)
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X4] :
        ( sK1 != k2_relset_1(sK0,sK1,sK3)
        & k1_xboole_0 != sK2
        & v2_funct_1(X4)
        & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK3)
      & k1_xboole_0 != sK2
      & v2_funct_1(sK4)
      & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(f61,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f735,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f734,f536])).

fof(f536,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f517,f209])).

fof(f209,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_14
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f517,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f514,f237])).

fof(f237,plain,
    ( sK1 = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f143,f224])).

fof(f224,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f171,f180])).

fof(f180,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f179,f60])).

fof(f60,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f47])).

fof(f179,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f174,f56])).

fof(f56,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f174,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f57,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f40])).

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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f171,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f57,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f143,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_7
  <=> k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f514,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f184,f108])).

fof(f108,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_1
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f113,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_2
  <=> v1_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f734,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f486,f460])).

fof(f460,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f451,f384])).

fof(f384,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f58,f296])).

fof(f296,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f293,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f293,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f181,f54])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f175,f55])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f58,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f451,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f389,f80])).

fof(f389,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f388,f52])).

fof(f388,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f387,f54])).

fof(f387,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f386,f55])).

fof(f386,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f385,f57])).

fof(f385,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f90,f296])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f486,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f480,f324])).

fof(f324,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1 ),
    inference(resolution,[],[f183,f150])).

fof(f150,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f183,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f108,f63])).

fof(f480,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f448,f186])).

fof(f186,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f185,f150])).

fof(f185,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f153,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f153,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f54,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f448,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f230,f148])).

fof(f148,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_8
  <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

% (24096)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f230,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f229,f113])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f226,f119])).

fof(f119,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_3
  <=> v1_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ v1_funct_1(k2_funct_1(sK4))
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_5 ),
    inference(superposition,[],[f74,f225])).

fof(f225,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f131,f224])).

fof(f131,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_5
  <=> k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f497,plain,
    ( ~ spl5_1
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f496])).

fof(f496,plain,
    ( $false
    | ~ spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f495,f150])).

fof(f495,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f494,f108])).

fof(f494,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f490,f205])).

fof(f205,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK4))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl5_13
  <=> r1_tarski(sK2,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f490,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f62,f460])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f210,plain,
    ( ~ spl5_13
    | spl5_14
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f201,f107,f207,f203])).

fof(f201,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ spl5_1 ),
    inference(resolution,[],[f188,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f187,f108])).

fof(f187,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f173,f71])).

fof(f173,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f57,f81])).

fof(f178,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f170,f109])).

fof(f109,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f170,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f57,f78])).

% (24108)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f149,plain,
    ( ~ spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f145,f147,f107])).

fof(f145,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f104,f55])).

fof(f104,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f59,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f59,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f144,plain,
    ( ~ spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f139,f141,f107])).

fof(f139,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f103,f55])).

fof(f103,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f132,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f127,f129,f107])).

fof(f127,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f101,f55])).

fof(f101,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f59,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f120,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f115,f117,f107])).

fof(f115,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f99,f55])).

fof(f99,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f59,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f114,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f105,f111,f107])).

fof(f105,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f98,f55])).

fof(f98,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f59,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:00:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (24109)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (24101)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (24102)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (24119)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (24097)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (24105)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (24117)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (24098)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (24115)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (24106)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (24104)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (24110)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (24100)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (24116)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (24114)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (24099)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.41/0.54  % (24097)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f738,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(avatar_sat_refutation,[],[f114,f120,f132,f144,f149,f178,f210,f497,f737])).
% 1.41/0.54  fof(f737,plain,(
% 1.41/0.54    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_14),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f736])).
% 1.41/0.54  fof(f736,plain,(
% 1.41/0.54    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_14)),
% 1.41/0.54    inference(subsumption_resolution,[],[f735,f223])).
% 1.41/0.54  fof(f223,plain,(
% 1.41/0.54    sK1 != k2_relat_1(sK3)),
% 1.41/0.54    inference(superposition,[],[f61,f152])).
% 1.41/0.54  fof(f152,plain,(
% 1.41/0.54    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.41/0.54    inference(resolution,[],[f54,f80])).
% 1.41/0.54  % (24107)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.41/0.54  fof(f80,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f37])).
% 1.41/0.54  fof(f37,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f13])).
% 1.41/0.54  fof(f13,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.41/0.54  fof(f54,plain,(
% 1.41/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f47,plain,(
% 1.41/0.54    (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f46,f45])).
% 1.41/0.54  fof(f45,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.41/0.54    inference(flattening,[],[f20])).
% 1.41/0.54  fof(f20,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.41/0.54    inference(ennf_transformation,[],[f18])).
% 1.41/0.54  fof(f18,negated_conjecture,(
% 1.41/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.41/0.54    inference(negated_conjecture,[],[f17])).
% 1.41/0.54  fof(f17,conjecture,(
% 1.41/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).
% 1.41/0.54  fof(f61,plain,(
% 1.41/0.54    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f735,plain,(
% 1.41/0.54    sK1 = k2_relat_1(sK3) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_14)),
% 1.41/0.54    inference(forward_demodulation,[],[f734,f536])).
% 1.41/0.54  fof(f536,plain,(
% 1.41/0.54    sK1 = k9_relat_1(k2_funct_1(sK4),sK2) | (~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_14)),
% 1.41/0.54    inference(forward_demodulation,[],[f517,f209])).
% 1.41/0.54  fof(f209,plain,(
% 1.41/0.54    sK2 = k2_relat_1(sK4) | ~spl5_14),
% 1.41/0.54    inference(avatar_component_clause,[],[f207])).
% 1.41/0.54  fof(f207,plain,(
% 1.41/0.54    spl5_14 <=> sK2 = k2_relat_1(sK4)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.41/0.54  fof(f517,plain,(
% 1.41/0.54    sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) | (~spl5_1 | ~spl5_2 | ~spl5_7)),
% 1.41/0.54    inference(forward_demodulation,[],[f514,f237])).
% 1.41/0.54  fof(f237,plain,(
% 1.41/0.54    sK1 = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) | ~spl5_7),
% 1.41/0.54    inference(forward_demodulation,[],[f143,f224])).
% 1.41/0.54  fof(f224,plain,(
% 1.41/0.54    sK1 = k1_relat_1(sK4)),
% 1.41/0.54    inference(forward_demodulation,[],[f171,f180])).
% 1.41/0.54  fof(f180,plain,(
% 1.41/0.54    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.41/0.54    inference(subsumption_resolution,[],[f179,f60])).
% 1.41/0.54  fof(f60,plain,(
% 1.41/0.54    k1_xboole_0 != sK2),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f179,plain,(
% 1.41/0.54    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.41/0.54    inference(subsumption_resolution,[],[f174,f56])).
% 1.41/0.54  fof(f56,plain,(
% 1.41/0.54    v1_funct_2(sK4,sK1,sK2)),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f174,plain,(
% 1.41/0.54    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.41/0.54    inference(resolution,[],[f57,f82])).
% 1.41/0.54  fof(f82,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f51])).
% 1.41/0.54  fof(f51,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(nnf_transformation,[],[f40])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(flattening,[],[f39])).
% 1.41/0.54  fof(f39,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f14])).
% 1.41/0.54  fof(f14,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.54  fof(f57,plain,(
% 1.41/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f171,plain,(
% 1.41/0.54    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 1.41/0.54    inference(resolution,[],[f57,f79])).
% 1.41/0.54  fof(f79,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f36])).
% 1.41/0.54  fof(f36,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f12])).
% 1.41/0.54  fof(f12,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.54  fof(f143,plain,(
% 1.41/0.54    k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) | ~spl5_7),
% 1.41/0.54    inference(avatar_component_clause,[],[f141])).
% 1.41/0.54  fof(f141,plain,(
% 1.41/0.54    spl5_7 <=> k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.41/0.54  fof(f514,plain,(
% 1.41/0.54    k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) | (~spl5_1 | ~spl5_2)),
% 1.41/0.54    inference(resolution,[],[f184,f108])).
% 1.41/0.54  fof(f108,plain,(
% 1.41/0.54    v1_relat_1(sK4) | ~spl5_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f107])).
% 1.41/0.54  fof(f107,plain,(
% 1.41/0.54    spl5_1 <=> v1_relat_1(sK4)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.41/0.54  fof(f184,plain,(
% 1.41/0.54    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0))) ) | ~spl5_2),
% 1.41/0.54    inference(resolution,[],[f113,f63])).
% 1.41/0.54  fof(f63,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f23])).
% 1.41/0.54  fof(f23,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f3])).
% 1.41/0.54  fof(f3,axiom,(
% 1.41/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.41/0.54  fof(f113,plain,(
% 1.41/0.54    v1_relat_1(k2_funct_1(sK4)) | ~spl5_2),
% 1.41/0.54    inference(avatar_component_clause,[],[f111])).
% 1.41/0.54  fof(f111,plain,(
% 1.41/0.54    spl5_2 <=> v1_relat_1(k2_funct_1(sK4))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.41/0.54  fof(f734,plain,(
% 1.41/0.54    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.41/0.54    inference(forward_demodulation,[],[f486,f460])).
% 1.41/0.54  fof(f460,plain,(
% 1.41/0.54    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.41/0.54    inference(forward_demodulation,[],[f451,f384])).
% 1.41/0.54  fof(f384,plain,(
% 1.41/0.54    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.41/0.54    inference(backward_demodulation,[],[f58,f296])).
% 1.41/0.54  fof(f296,plain,(
% 1.41/0.54    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.41/0.54    inference(subsumption_resolution,[],[f293,f52])).
% 1.41/0.54  fof(f52,plain,(
% 1.41/0.54    v1_funct_1(sK3)),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f293,plain,(
% 1.41/0.54    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 1.41/0.54    inference(resolution,[],[f181,f54])).
% 1.41/0.54  fof(f181,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(X2)) )),
% 1.41/0.54    inference(subsumption_resolution,[],[f175,f55])).
% 1.41/0.54  fof(f55,plain,(
% 1.41/0.54    v1_funct_1(sK4)),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f175,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.41/0.54    inference(resolution,[],[f57,f88])).
% 1.41/0.54  fof(f88,plain,(
% 1.41/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f42])).
% 1.41/0.54  fof(f42,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.41/0.54    inference(flattening,[],[f41])).
% 1.41/0.54  fof(f41,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.41/0.54    inference(ennf_transformation,[],[f16])).
% 1.41/0.54  fof(f16,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.41/0.54  fof(f58,plain,(
% 1.41/0.54    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f451,plain,(
% 1.41/0.54    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.41/0.54    inference(resolution,[],[f389,f80])).
% 1.41/0.54  fof(f389,plain,(
% 1.41/0.54    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.54    inference(subsumption_resolution,[],[f388,f52])).
% 1.41/0.54  fof(f388,plain,(
% 1.41/0.54    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3)),
% 1.41/0.54    inference(subsumption_resolution,[],[f387,f54])).
% 1.41/0.54  fof(f387,plain,(
% 1.41/0.54    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.41/0.54    inference(subsumption_resolution,[],[f386,f55])).
% 1.41/0.54  fof(f386,plain,(
% 1.41/0.54    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.41/0.54    inference(subsumption_resolution,[],[f385,f57])).
% 1.41/0.54  fof(f385,plain,(
% 1.41/0.54    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.41/0.54    inference(superposition,[],[f90,f296])).
% 1.41/0.54  fof(f90,plain,(
% 1.41/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f44])).
% 1.41/0.54  fof(f44,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.41/0.54    inference(flattening,[],[f43])).
% 1.41/0.54  fof(f43,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.41/0.54    inference(ennf_transformation,[],[f15])).
% 1.41/0.54  fof(f15,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.41/0.54  fof(f486,plain,(
% 1.41/0.54    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.41/0.54    inference(forward_demodulation,[],[f480,f324])).
% 1.41/0.54  fof(f324,plain,(
% 1.41/0.54    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) | ~spl5_1),
% 1.41/0.54    inference(resolution,[],[f183,f150])).
% 1.41/0.54  fof(f150,plain,(
% 1.41/0.54    v1_relat_1(sK3)),
% 1.41/0.54    inference(resolution,[],[f54,f78])).
% 1.41/0.54  fof(f78,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f35])).
% 1.41/0.54  fof(f35,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f10])).
% 1.41/0.54  fof(f10,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.54  fof(f183,plain,(
% 1.41/0.54    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0))) ) | ~spl5_1),
% 1.41/0.54    inference(resolution,[],[f108,f63])).
% 1.41/0.54  fof(f480,plain,(
% 1.41/0.54    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.41/0.54    inference(resolution,[],[f448,f186])).
% 1.41/0.54  fof(f186,plain,(
% 1.41/0.54    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.41/0.54    inference(subsumption_resolution,[],[f185,f150])).
% 1.41/0.54  fof(f185,plain,(
% 1.41/0.54    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.41/0.54    inference(resolution,[],[f153,f71])).
% 1.41/0.54  fof(f71,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f48])).
% 1.41/0.54  fof(f48,plain,(
% 1.41/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(nnf_transformation,[],[f30])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f2])).
% 1.41/0.54  fof(f2,axiom,(
% 1.41/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.41/0.54  fof(f153,plain,(
% 1.41/0.54    v5_relat_1(sK3,sK1)),
% 1.41/0.54    inference(resolution,[],[f54,f81])).
% 1.41/0.54  fof(f81,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f38])).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f19])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.41/0.54    inference(pure_predicate_removal,[],[f11])).
% 1.41/0.54  fof(f11,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.41/0.54  fof(f448,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0) ) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.41/0.54    inference(forward_demodulation,[],[f230,f148])).
% 1.41/0.54  fof(f148,plain,(
% 1.41/0.54    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)) ) | ~spl5_8),
% 1.41/0.54    inference(avatar_component_clause,[],[f147])).
% 1.41/0.54  fof(f147,plain,(
% 1.41/0.54    spl5_8 <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.41/0.54  % (24096)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.41/0.54  fof(f230,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 1.41/0.54    inference(subsumption_resolution,[],[f229,f113])).
% 1.41/0.54  fof(f229,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~v1_relat_1(k2_funct_1(sK4))) ) | (~spl5_3 | ~spl5_5)),
% 1.41/0.54    inference(subsumption_resolution,[],[f226,f119])).
% 1.41/0.54  fof(f119,plain,(
% 1.41/0.54    v1_funct_1(k2_funct_1(sK4)) | ~spl5_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f117])).
% 1.41/0.54  fof(f117,plain,(
% 1.41/0.54    spl5_3 <=> v1_funct_1(k2_funct_1(sK4))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.41/0.54  fof(f226,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))) ) | ~spl5_5),
% 1.41/0.54    inference(superposition,[],[f74,f225])).
% 1.41/0.54  fof(f225,plain,(
% 1.41/0.54    sK1 = k2_relat_1(k2_funct_1(sK4)) | ~spl5_5),
% 1.41/0.54    inference(backward_demodulation,[],[f131,f224])).
% 1.41/0.54  fof(f131,plain,(
% 1.41/0.54    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~spl5_5),
% 1.41/0.54    inference(avatar_component_clause,[],[f129])).
% 1.41/0.54  fof(f129,plain,(
% 1.41/0.54    spl5_5 <=> k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.41/0.54  fof(f74,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f34])).
% 1.41/0.54  fof(f34,plain,(
% 1.41/0.54    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(flattening,[],[f33])).
% 1.41/0.54  fof(f33,plain,(
% 1.41/0.54    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.41/0.54    inference(ennf_transformation,[],[f6])).
% 1.41/0.54  fof(f6,axiom,(
% 1.41/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.41/0.54  fof(f497,plain,(
% 1.41/0.54    ~spl5_1 | spl5_13),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f496])).
% 1.41/0.54  fof(f496,plain,(
% 1.41/0.54    $false | (~spl5_1 | spl5_13)),
% 1.41/0.54    inference(subsumption_resolution,[],[f495,f150])).
% 1.41/0.54  fof(f495,plain,(
% 1.41/0.54    ~v1_relat_1(sK3) | (~spl5_1 | spl5_13)),
% 1.41/0.54    inference(subsumption_resolution,[],[f494,f108])).
% 1.41/0.54  fof(f494,plain,(
% 1.41/0.54    ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | spl5_13),
% 1.41/0.54    inference(subsumption_resolution,[],[f490,f205])).
% 1.41/0.54  fof(f205,plain,(
% 1.41/0.54    ~r1_tarski(sK2,k2_relat_1(sK4)) | spl5_13),
% 1.41/0.54    inference(avatar_component_clause,[],[f203])).
% 1.41/0.54  fof(f203,plain,(
% 1.41/0.54    spl5_13 <=> r1_tarski(sK2,k2_relat_1(sK4))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.41/0.54  fof(f490,plain,(
% 1.41/0.54    r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 1.41/0.54    inference(superposition,[],[f62,f460])).
% 1.41/0.54  fof(f62,plain,(
% 1.41/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f22])).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f4])).
% 1.41/0.54  fof(f4,axiom,(
% 1.41/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.41/0.54  fof(f210,plain,(
% 1.41/0.54    ~spl5_13 | spl5_14 | ~spl5_1),
% 1.41/0.54    inference(avatar_split_clause,[],[f201,f107,f207,f203])).
% 1.41/0.54  fof(f201,plain,(
% 1.41/0.54    sK2 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~spl5_1),
% 1.41/0.54    inference(resolution,[],[f188,f77])).
% 1.41/0.54  fof(f77,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f50])).
% 1.41/0.54  fof(f50,plain,(
% 1.41/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.54    inference(flattening,[],[f49])).
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.54    inference(nnf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.54  fof(f188,plain,(
% 1.41/0.54    r1_tarski(k2_relat_1(sK4),sK2) | ~spl5_1),
% 1.41/0.54    inference(subsumption_resolution,[],[f187,f108])).
% 1.41/0.54  fof(f187,plain,(
% 1.41/0.54    r1_tarski(k2_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(resolution,[],[f173,f71])).
% 1.41/0.54  fof(f173,plain,(
% 1.41/0.54    v5_relat_1(sK4,sK2)),
% 1.41/0.54    inference(resolution,[],[f57,f81])).
% 1.41/0.54  fof(f178,plain,(
% 1.41/0.54    spl5_1),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f177])).
% 1.41/0.54  fof(f177,plain,(
% 1.41/0.54    $false | spl5_1),
% 1.41/0.54    inference(subsumption_resolution,[],[f170,f109])).
% 1.41/0.54  fof(f109,plain,(
% 1.41/0.54    ~v1_relat_1(sK4) | spl5_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f107])).
% 1.41/0.54  fof(f170,plain,(
% 1.41/0.54    v1_relat_1(sK4)),
% 1.41/0.54    inference(resolution,[],[f57,f78])).
% 1.41/0.54  % (24108)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.41/0.54  fof(f149,plain,(
% 1.41/0.54    ~spl5_1 | spl5_8),
% 1.41/0.54    inference(avatar_split_clause,[],[f145,f147,f107])).
% 1.41/0.54  fof(f145,plain,(
% 1.41/0.54    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_relat_1(sK4)) )),
% 1.41/0.54    inference(subsumption_resolution,[],[f104,f55])).
% 1.41/0.54  fof(f104,plain,(
% 1.41/0.54    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.41/0.54    inference(resolution,[],[f59,f73])).
% 1.41/0.54  fof(f73,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f32])).
% 1.41/0.54  fof(f32,plain,(
% 1.41/0.54    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(flattening,[],[f31])).
% 1.41/0.54  fof(f31,plain,(
% 1.41/0.54    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.41/0.54    inference(ennf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,axiom,(
% 1.41/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 1.41/0.54  fof(f59,plain,(
% 1.41/0.54    v2_funct_1(sK4)),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f144,plain,(
% 1.41/0.54    ~spl5_1 | spl5_7),
% 1.41/0.54    inference(avatar_split_clause,[],[f139,f141,f107])).
% 1.41/0.54  fof(f139,plain,(
% 1.41/0.54    k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(subsumption_resolution,[],[f103,f55])).
% 1.41/0.54  fof(f103,plain,(
% 1.41/0.54    k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(resolution,[],[f59,f70])).
% 1.41/0.54  fof(f70,plain,(
% 1.41/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(flattening,[],[f28])).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,axiom,(
% 1.41/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.41/0.54  fof(f132,plain,(
% 1.41/0.54    ~spl5_1 | spl5_5),
% 1.41/0.54    inference(avatar_split_clause,[],[f127,f129,f107])).
% 1.41/0.54  fof(f127,plain,(
% 1.41/0.54    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(subsumption_resolution,[],[f101,f55])).
% 1.41/0.54  fof(f101,plain,(
% 1.41/0.54    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(resolution,[],[f59,f68])).
% 1.41/0.54  fof(f68,plain,(
% 1.41/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f27])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(flattening,[],[f26])).
% 1.41/0.54  fof(f26,plain,(
% 1.41/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f8])).
% 1.41/0.54  fof(f8,axiom,(
% 1.41/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.41/0.54  fof(f120,plain,(
% 1.41/0.54    ~spl5_1 | spl5_3),
% 1.41/0.54    inference(avatar_split_clause,[],[f115,f117,f107])).
% 1.41/0.54  fof(f115,plain,(
% 1.41/0.54    v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(subsumption_resolution,[],[f99,f55])).
% 1.41/0.54  fof(f99,plain,(
% 1.41/0.54    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(resolution,[],[f59,f65])).
% 1.41/0.54  fof(f65,plain,(
% 1.41/0.54    ( ! [X0] : (~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f25])).
% 1.41/0.54  fof(f25,plain,(
% 1.41/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(flattening,[],[f24])).
% 1.41/0.54  fof(f24,plain,(
% 1.41/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.41/0.54  fof(f114,plain,(
% 1.41/0.54    ~spl5_1 | spl5_2),
% 1.41/0.54    inference(avatar_split_clause,[],[f105,f111,f107])).
% 1.41/0.54  fof(f105,plain,(
% 1.41/0.54    v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(subsumption_resolution,[],[f98,f55])).
% 1.41/0.54  fof(f98,plain,(
% 1.41/0.54    v1_relat_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.41/0.54    inference(resolution,[],[f59,f64])).
% 1.41/0.54  fof(f64,plain,(
% 1.41/0.54    ( ! [X0] : (~v2_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f25])).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (24097)------------------------------
% 1.41/0.54  % (24097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (24097)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (24097)Memory used [KB]: 11001
% 1.41/0.54  % (24097)Time elapsed: 0.106 s
% 1.41/0.54  % (24097)------------------------------
% 1.41/0.54  % (24097)------------------------------
% 1.41/0.54  % (24095)Success in time 0.181 s
%------------------------------------------------------------------------------
