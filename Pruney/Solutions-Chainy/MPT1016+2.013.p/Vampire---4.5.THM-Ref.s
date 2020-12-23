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
% DateTime   : Thu Dec  3 13:05:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  192 (11312081 expanded)
%              Number of leaves         :    8 (2722046 expanded)
%              Depth                    :  138
%              Number of atoms          :  900 (104594973 expanded)
%              Number of equality atoms :  454 (34445419 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f469,plain,(
    $false ),
    inference(subsumption_resolution,[],[f468,f52])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f468,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f467,f26])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f467,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f464,f447])).

fof(f447,plain,(
    ~ v2_funct_1(sK1) ),
    inference(trivial_inequality_removal,[],[f438])).

fof(f438,plain,
    ( sK2 != sK2
    | ~ v2_funct_1(sK1) ),
    inference(superposition,[],[f33,f436])).

fof(f436,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f435,f395])).

fof(f395,plain,
    ( v2_funct_1(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f394,f52])).

fof(f394,plain,
    ( v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f391,f26])).

fof(f391,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f389])).

fof(f389,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = sK3 ),
    inference(superposition,[],[f38,f381])).

fof(f381,plain,
    ( sK4(sK1) = sK5(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f380,f356])).

fof(f356,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f355,f266])).

fof(f266,plain,
    ( r2_hidden(sK4(sK1),k1_xboole_0)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f265,f52])).

fof(f265,plain,
    ( r2_hidden(sK4(sK1),k1_xboole_0)
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f260,f26])).

fof(f260,plain,
    ( r2_hidden(sK4(sK1),k1_xboole_0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f35,f251])).

fof(f251,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(superposition,[],[f212,f248])).

fof(f248,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f242,f208])).

fof(f208,plain,(
    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f27,f206])).

fof(f206,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f205,f188])).

fof(f188,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( sK2 != sK2
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f33,f177])).

fof(f177,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f176,f148])).

fof(f148,plain,
    ( v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f147,f52])).

fof(f147,plain,
    ( v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f145,f26])).

fof(f145,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(superposition,[],[f38,f138])).

fof(f138,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f137,f120])).

fof(f120,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f119,f76])).

% (14683)Refutation not found, incomplete strategy% (14683)------------------------------
% (14683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14683)Termination reason: Refutation not found, incomplete strategy

% (14683)Memory used [KB]: 10618
% (14683)Time elapsed: 0.095 s
% (14683)------------------------------
% (14683)------------------------------
fof(f76,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f75,f52])).

fof(f75,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f72,f26])).

fof(f72,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f35,f65])).

fof(f65,plain,
    ( sK0 = k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f63,f53])).

fof(f53,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f63,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f62,f27])).

fof(f62,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f119,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0 ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X0
      | ~ r2_hidden(X0,sK0)
      | v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f109,f74])).

fof(f74,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f73,f52])).

fof(f73,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f71,f26])).

fof(f71,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f36,f65])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f109,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X0
      | ~ r2_hidden(sK5(sK1),sK0)
      | ~ r2_hidden(X0,sK0)
      | v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f29,f106])).

fof(f106,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f105,f52])).

fof(f105,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | k1_xboole_0 = sK0
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f104,f26])).

fof(f104,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f102,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,
    ( ~ v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f101,f33])).

fof(f101,plain,
    ( k1_xboole_0 = sK0
    | sK4(sK1) = sK5(sK1)
    | sK2 = sK3
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f100,f30])).

fof(f30,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,
    ( ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = sK0
    | sK4(sK1) = sK5(sK1)
    | sK2 = sK3
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1)
      | sK3 = X0
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ) ),
    inference(subsumption_resolution,[],[f96,f52])).

fof(f96,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1)
      | sK3 = X0
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f95,f26])).

fof(f95,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1)
      | sK3 = X0
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f94,f37])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_funct_1(sK1)
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1)
      | sK3 = X0 ) ),
    inference(resolution,[],[f93,f31])).

fof(f31,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,sK0)
      | sK3 = X0
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1) ) ),
    inference(subsumption_resolution,[],[f92,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,sK0)
      | sK3 = X0
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1) ) ),
    inference(superposition,[],[f29,f83])).

fof(f83,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = sK0
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f82,f32])).

fof(f32,plain,
    ( ~ v2_funct_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | v2_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f80,f76])).

fof(f80,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X0
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f77,f32])).

fof(f77,plain,(
    ! [X0] :
      ( v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK5(sK1) = X0
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(resolution,[],[f74,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1),sK0)
      | sK5(sK1) = X0
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f57,f32])).

fof(f57,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X0
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK5(sK1),sK0)
      | v2_funct_1(sK1)
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(superposition,[],[f29,f56])).

fof(f56,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f55,f52])).

fof(f55,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f54,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f37,f32])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,sK0)
      | sK3 = X0
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,sK0)
      | sK3 = X0
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f89,f65])).

fof(f89,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3,k1_relat_1(sK1))
      | sK3 = X2
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1) ) ),
    inference(subsumption_resolution,[],[f88,f52])).

fof(f88,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1) ) ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f86,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1) ) ),
    inference(superposition,[],[f34,f83])).

fof(f34,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | X4 = X5
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f137,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f133,f30])).

fof(f133,plain,
    ( ~ r2_hidden(sK2,sK0)
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1)
      | ~ r2_hidden(X0,sK0)
      | sK3 = X0 ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0] :
      ( sK4(sK1) = sK5(sK1)
      | k1_xboole_0 = sK0
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | sK4(sK1) = sK5(sK1)
      | sK3 = X0 ) ),
    inference(resolution,[],[f120,f94])).

fof(f176,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f174,f30])).

fof(f174,plain,
    ( ~ r2_hidden(sK2,sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK2,sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(equality_resolution,[],[f168])).

fof(f168,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | ~ r2_hidden(X0,sK0)
      | sK2 = sK3
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f167,f148])).

fof(f167,plain,(
    ! [X0] :
      ( sK3 = X0
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | sK2 = sK3
      | k1_xboole_0 = sK0
      | ~ v2_funct_1(sK1) ) ),
    inference(resolution,[],[f166,f31])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,sK0)
      | sK3 = X0
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | sK2 = sK3
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,sK0)
      | sK3 = X0
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,sK0)
      | sK2 = sK3
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f164,f65])).

fof(f164,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3,k1_relat_1(sK1))
      | sK3 = X2
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | sK2 = sK3
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f163,f148])).

fof(f163,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | sK2 = sK3
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f162,f52])).

fof(f162,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK2 = sK3
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f160,f26])).

fof(f160,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK2 = sK3
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f34,f151])).

fof(f151,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f148,f32])).

fof(f205,plain,
    ( v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f204,f52])).

fof(f204,plain,
    ( v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f202,f26])).

fof(f202,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f38,f192])).

fof(f192,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,
    ( k1_xboole_0 = sK0
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f188,f120])).

fof(f27,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f242,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(resolution,[],[f209,f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f209,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f28,f206])).

fof(f212,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(superposition,[],[f53,f206])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f355,plain,
    ( ~ r2_hidden(sK4(sK1),k1_xboole_0)
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,
    ( ~ r2_hidden(sK4(sK1),k1_xboole_0)
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1) ),
    inference(equality_resolution,[],[f336])).

fof(f336,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,k1_xboole_0)
      | sK5(sK1) = X0
      | v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(subsumption_resolution,[],[f335,f264])).

fof(f264,plain,
    ( r2_hidden(sK5(sK1),k1_xboole_0)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f263,f52])).

fof(f263,plain,
    ( r2_hidden(sK5(sK1),k1_xboole_0)
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f259,f26])).

fof(f259,plain,
    ( r2_hidden(sK5(sK1),k1_xboole_0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f36,f251])).

fof(f335,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1),k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X0
      | v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(forward_demodulation,[],[f334,f206])).

fof(f334,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X0
      | ~ r2_hidden(sK5(sK1),sK0)
      | v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(forward_demodulation,[],[f322,f206])).

fof(f322,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X0
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK5(sK1),sK0)
      | v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(superposition,[],[f29,f321])).

fof(f321,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f320,f52])).

fof(f320,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f318,f26])).

fof(f318,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f314,f37])).

fof(f314,plain,
    ( ~ v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f313,f33])).

fof(f313,plain,
    ( sK2 = sK3
    | sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f312,f210])).

fof(f210,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ v2_funct_1(sK1) ),
    inference(superposition,[],[f30,f206])).

fof(f312,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | sK2 = sK3
    | sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(equality_resolution,[],[f303])).

fof(f303,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(X2,k1_xboole_0)
      | sK4(sK1) = sK5(sK1)
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ) ),
    inference(subsumption_resolution,[],[f302,f52])).

fof(f302,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(X2,k1_xboole_0)
      | sK4(sK1) = sK5(sK1)
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f300,f26])).

fof(f300,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(X2,k1_xboole_0)
      | sK4(sK1) = sK5(sK1)
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f294,f37])).

fof(f294,plain,(
    ! [X2] :
      ( ~ v2_funct_1(sK1)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(X2,k1_xboole_0)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(forward_demodulation,[],[f293,f251])).

fof(f293,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(subsumption_resolution,[],[f292,f211])).

fof(f211,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ v2_funct_1(sK1) ),
    inference(superposition,[],[f31,f206])).

fof(f292,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3,k1_xboole_0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(forward_demodulation,[],[f291,f251])).

fof(f291,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(subsumption_resolution,[],[f290,f52])).

fof(f290,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(subsumption_resolution,[],[f284,f26])).

fof(f284,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(superposition,[],[f34,f278])).

fof(f278,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f277,f32])).

fof(f277,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f276,f266])).

fof(f276,plain,
    ( ~ r2_hidden(sK4(sK1),k1_xboole_0)
    | sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(equality_resolution,[],[f272])).

fof(f272,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,k1_xboole_0)
      | sK5(sK1) = X0
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f269,f32])).

fof(f269,plain,(
    ! [X0] :
      ( v2_funct_1(sK1)
      | sK5(sK1) = X0
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(resolution,[],[f264,f213])).

fof(f213,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1),k1_xboole_0)
      | sK5(sK1) = X0
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(superposition,[],[f61,f206])).

fof(f380,plain,
    ( sK2 = sK3
    | sK4(sK1) = sK5(sK1)
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f377,f210])).

fof(f377,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | sK2 = sK3
    | sK4(sK1) = sK5(sK1) ),
    inference(equality_resolution,[],[f365])).

fof(f365,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK4(sK1) = sK5(sK1)
      | sK3 = X0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,(
    ! [X0] :
      ( sK4(sK1) = sK5(sK1)
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | ~ r2_hidden(X0,k1_xboole_0)
      | sK4(sK1) = sK5(sK1) ) ),
    inference(resolution,[],[f356,f294])).

fof(f38,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f435,plain,
    ( sK2 = sK3
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f434,f210])).

fof(f434,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | sK2 = sK3 ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | sK2 = sK3
    | sK2 = sK3 ),
    inference(equality_resolution,[],[f424])).

fof(f424,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | sK3 = X0
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f422,f395])).

fof(f422,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | sK2 = sK3
      | ~ v2_funct_1(sK1) ) ),
    inference(resolution,[],[f416,f211])).

fof(f416,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | sK2 = sK3 ) ),
    inference(forward_demodulation,[],[f415,f251])).

fof(f415,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3,k1_xboole_0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | sK2 = sK3 ) ),
    inference(forward_demodulation,[],[f414,f251])).

fof(f414,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f413,f395])).

fof(f413,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f412,f52])).

fof(f412,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f410,f26])).

fof(f410,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
      | sK3 = X2
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK2 = sK3 ) ),
    inference(superposition,[],[f34,f401])).

fof(f401,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f395,f32])).

fof(f33,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f464,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f38,f449])).

fof(f449,plain,(
    sK4(sK1) = sK5(sK1) ),
    inference(resolution,[],[f447,f356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (14677)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (14677)Refutation not found, incomplete strategy% (14677)------------------------------
% 0.20/0.48  % (14677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (14693)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.48  % (14677)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (14677)Memory used [KB]: 10618
% 0.20/0.48  % (14677)Time elapsed: 0.070 s
% 0.20/0.48  % (14677)------------------------------
% 0.20/0.48  % (14677)------------------------------
% 0.20/0.49  % (14683)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (14693)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f469,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f468,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f39,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.50    inference(rectify,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.50    inference(flattening,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f468,plain,(
% 0.20/0.50    ~v1_relat_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f467,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    v1_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f467,plain,(
% 0.20/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f464,f447])).
% 0.20/0.50  fof(f447,plain,(
% 0.20/0.50    ~v2_funct_1(sK1)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f438])).
% 0.20/0.50  fof(f438,plain,(
% 0.20/0.50    sK2 != sK2 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(superposition,[],[f33,f436])).
% 0.20/0.50  fof(f436,plain,(
% 0.20/0.50    sK2 = sK3),
% 0.20/0.50    inference(subsumption_resolution,[],[f435,f395])).
% 0.20/0.50  fof(f395,plain,(
% 0.20/0.50    v2_funct_1(sK1) | sK2 = sK3),
% 0.20/0.50    inference(subsumption_resolution,[],[f394,f52])).
% 0.20/0.50  fof(f394,plain,(
% 0.20/0.50    v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = sK3),
% 0.20/0.50    inference(subsumption_resolution,[],[f391,f26])).
% 0.20/0.50  fof(f391,plain,(
% 0.20/0.50    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = sK3),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f389])).
% 0.20/0.50  fof(f389,plain,(
% 0.20/0.50    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = sK3),
% 0.20/0.50    inference(superposition,[],[f38,f381])).
% 0.20/0.50  fof(f381,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | sK2 = sK3),
% 0.20/0.50    inference(subsumption_resolution,[],[f380,f356])).
% 0.20/0.50  fof(f356,plain,(
% 0.20/0.50    v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f355,f266])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),k1_xboole_0) | v2_funct_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f265,f52])).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),k1_xboole_0) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f260,f26])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),k1_xboole_0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(superposition,[],[f35,f251])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK1)),
% 0.20/0.50    inference(superposition,[],[f212,f248])).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f242,f208])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(superposition,[],[f27,f206])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f205,f188])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f179])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    sK2 != sK2 | ~v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f33,f177])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    sK2 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f176,f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.20/0.50    inference(subsumption_resolution,[],[f147,f52])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    v2_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.20/0.50    inference(subsumption_resolution,[],[f145,f26])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f143])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.20/0.50    inference(superposition,[],[f38,f138])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.20/0.50    inference(subsumption_resolution,[],[f137,f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    v2_funct_1(sK1) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f119,f76])).
% 0.20/0.50  % (14683)Refutation not found, incomplete strategy% (14683)------------------------------
% 0.20/0.50  % (14683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14683)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (14683)Memory used [KB]: 10618
% 0.20/0.50  % (14683)Time elapsed: 0.095 s
% 0.20/0.50  % (14683)------------------------------
% 0.20/0.50  % (14683)------------------------------
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f75,f52])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f72,f26])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f35,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f63,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f40,f28])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f62,f27])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.50    inference(resolution,[],[f41,f28])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | ~r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | ~r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(equality_resolution,[],[f113])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0) | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f73,f52])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f26])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f36,f65])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(rectify,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(X0,sK0) | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(superposition,[],[f29,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f52])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | k1_xboole_0 = sK0 | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f104,f26])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f102,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f101,f33])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | sK2 = sK3 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f100,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ~r2_hidden(sK2,sK0) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | sK2 = sK3 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.20/0.50    inference(equality_resolution,[],[f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | sK3 = X0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f52])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | sK3 = X0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f95,f26])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | sK3 = X0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.50    inference(resolution,[],[f94,f37])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(sK1) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | sK3 = X0) )),
% 0.20/0.50    inference(resolution,[],[f93,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3,sK0) | sK3 = X0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f92,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3,sK0) | sK3 = X0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(superposition,[],[f29,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f82,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | v2_funct_1(sK1)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f80,f76])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ~r2_hidden(sK4(sK1),sK0) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(equality_resolution,[],[f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f77,f32])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK5(sK1) = X0 | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.20/0.50    inference(resolution,[],[f74,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK5(sK1),sK0) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f57,f32])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0) | ~r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.20/0.50    inference(superposition,[],[f29,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f55,f52])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f54,f26])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(resolution,[],[f37,f32])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3,sK0) | sK3 = X0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3,sK0) | sK3 = X0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(superposition,[],[f89,f65])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(sK3,k1_relat_1(sK1)) | sK3 = X2 | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f88,f52])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f86,f26])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(superposition,[],[f34,f83])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X4,X5] : (k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | X4 = X5 | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f133,f30])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ~r2_hidden(sK2,sK0) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.20/0.50    inference(equality_resolution,[],[f124])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | ~r2_hidden(X0,sK0) | sK3 = X0) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f122])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X0] : (sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | sK3 = X0) )),
% 0.20/0.50    inference(resolution,[],[f120,f94])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    sK2 = sK3 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f174,f30])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    ~r2_hidden(sK2,sK0) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f173])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    sK2 = sK3 | ~r2_hidden(sK2,sK0) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.50    inference(equality_resolution,[],[f168])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(X0,sK0) | sK2 = sK3 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f167,f148])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    ( ! [X0] : (sK3 = X0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | sK2 = sK3 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)) )),
% 0.20/0.50    inference(resolution,[],[f166,f31])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3,sK0) | sK3 = X0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | sK2 = sK3 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3,sK0) | sK3 = X0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(superposition,[],[f164,f65])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(sK3,k1_relat_1(sK1)) | sK3 = X2 | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | ~r2_hidden(X2,k1_relat_1(sK1)) | sK2 = sK3 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f163,f148])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | sK2 = sK3 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f52])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = sK3 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f160,f26])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = sK3 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(superposition,[],[f34,f151])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f148,f32])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f204,f52])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    v2_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f202,f26])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f200])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f38,f192])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f190])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f188,f120])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.20/0.50    inference(resolution,[],[f209,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.50    inference(equality_resolution,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.50    inference(superposition,[],[f28,f206])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.20/0.50    inference(superposition,[],[f53,f206])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    ~r2_hidden(sK4(sK1),k1_xboole_0) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f354])).
% 0.20/0.50  fof(f354,plain,(
% 0.20/0.50    ~r2_hidden(sK4(sK1),k1_xboole_0) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(equality_resolution,[],[f336])).
% 0.20/0.50  fof(f336,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,k1_xboole_0) | sK5(sK1) = X0 | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f335,f264])).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),k1_xboole_0) | v2_funct_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f263,f52])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),k1_xboole_0) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f259,f26])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),k1_xboole_0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(superposition,[],[f36,f251])).
% 0.20/0.50  fof(f335,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK5(sK1),k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f334,f206])).
% 0.20/0.50  fof(f334,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f322,f206])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0) | ~r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(superposition,[],[f29,f321])).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f320,f52])).
% 0.20/0.50  fof(f320,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f318,f26])).
% 0.20/0.50  fof(f318,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f317])).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f314,f37])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f313,f33])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    sK2 = sK3 | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f312,f210])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    r2_hidden(sK2,k1_xboole_0) | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(superposition,[],[f30,f206])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    ~r2_hidden(sK2,k1_xboole_0) | sK2 = sK3 | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.20/0.50    inference(equality_resolution,[],[f303])).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(X2,k1_xboole_0) | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f302,f52])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(X2,k1_xboole_0) | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f300,f26])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(X2,k1_xboole_0) | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.50    inference(resolution,[],[f294,f37])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    ( ! [X2] : (~v2_funct_1(sK1) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(X2,k1_xboole_0) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f293,f251])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f292,f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    r2_hidden(sK3,k1_xboole_0) | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(superposition,[],[f31,f206])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(sK3,k1_xboole_0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f291,f251])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f290,f52])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f284,f26])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(superposition,[],[f34,f278])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f277,f32])).
% 0.20/0.50  fof(f277,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f276,f266])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    ~r2_hidden(sK4(sK1),k1_xboole_0) | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(equality_resolution,[],[f272])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,k1_xboole_0) | sK5(sK1) = X0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f269,f32])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(sK1) | sK5(sK1) = X0 | ~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.20/0.50    inference(resolution,[],[f264,f213])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK5(sK1),k1_xboole_0) | sK5(sK1) = X0 | ~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.20/0.50    inference(superposition,[],[f61,f206])).
% 0.20/0.50  fof(f380,plain,(
% 0.20/0.50    sK2 = sK3 | sK4(sK1) = sK5(sK1) | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f377,f210])).
% 0.20/0.50  fof(f377,plain,(
% 0.20/0.50    ~r2_hidden(sK2,k1_xboole_0) | sK2 = sK3 | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(equality_resolution,[],[f365])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK4(sK1) = sK5(sK1) | sK3 = X0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f358])).
% 0.20/0.50  fof(f358,plain,(
% 0.20/0.50    ( ! [X0] : (sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(X0,k1_xboole_0) | sK4(sK1) = sK5(sK1)) )),
% 0.20/0.50    inference(resolution,[],[f356,f294])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    sK2 = sK3 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f434,f210])).
% 0.20/0.50  fof(f434,plain,(
% 0.20/0.50    ~r2_hidden(sK2,k1_xboole_0) | sK2 = sK3),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f433])).
% 0.20/0.50  fof(f433,plain,(
% 0.20/0.50    ~r2_hidden(sK2,k1_xboole_0) | sK2 = sK3 | sK2 = sK3),
% 0.20/0.50    inference(equality_resolution,[],[f424])).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_xboole_0) | sK3 = X0 | sK2 = sK3) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f422,f395])).
% 0.20/0.50  fof(f422,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | sK2 = sK3 | ~v2_funct_1(sK1)) )),
% 0.20/0.50    inference(resolution,[],[f416,f211])).
% 0.20/0.50  fof(f416,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(sK3,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | sK2 = sK3) )),
% 0.20/0.50    inference(forward_demodulation,[],[f415,f251])).
% 0.20/0.50  fof(f415,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(sK3,k1_xboole_0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(X2,k1_relat_1(sK1)) | sK2 = sK3) )),
% 0.20/0.50    inference(forward_demodulation,[],[f414,f251])).
% 0.20/0.50  fof(f414,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | sK2 = sK3) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f413,f395])).
% 0.20/0.50  fof(f413,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | sK2 = sK3) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f412,f52])).
% 0.20/0.50  fof(f412,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = sK3) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f410,f26])).
% 0.20/0.50  fof(f410,plain,(
% 0.20/0.50    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | sK3 = X2 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = sK3) )),
% 0.20/0.50    inference(superposition,[],[f34,f401])).
% 0.20/0.50  fof(f401,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | sK2 = sK3),
% 0.20/0.50    inference(resolution,[],[f395,f32])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f464,plain,(
% 0.20/0.50    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f462])).
% 0.20/0.50  fof(f462,plain,(
% 0.20/0.50    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(superposition,[],[f38,f449])).
% 0.20/0.50  fof(f449,plain,(
% 0.20/0.50    sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(resolution,[],[f447,f356])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (14693)------------------------------
% 0.20/0.50  % (14693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14693)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (14693)Memory used [KB]: 1663
% 0.20/0.50  % (14693)Time elapsed: 0.093 s
% 0.20/0.50  % (14693)------------------------------
% 0.20/0.50  % (14693)------------------------------
% 0.20/0.50  % (14676)Success in time 0.146 s
%------------------------------------------------------------------------------
