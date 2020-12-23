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
% DateTime   : Thu Dec  3 13:01:08 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 419 expanded)
%              Number of leaves         :   20 ( 131 expanded)
%              Depth                    :   17
%              Number of atoms          :  468 (2689 expanded)
%              Number of equality atoms :  134 ( 516 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f118,f120,f161,f246,f265,f319])).

fof(f319,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_11
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f317,f162])).

fof(f162,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f95,f104])).

fof(f104,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f95,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f49,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f29,f28])).

% (17296)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f317,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl8_2
    | spl8_11
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f316,f198])).

fof(f198,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl8_2 ),
    inference(forward_demodulation,[],[f191,f197])).

fof(f197,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f196,f107])).

fof(f107,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f196,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f189,f51])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f189,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f52,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f191,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f52,f74])).

fof(f316,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f315,f192])).

fof(f192,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f52,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f315,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f314,f50])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f314,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f313,f96])).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f49,f73])).

fof(f313,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f312,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f312,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f311,f240])).

fof(f240,plain,
    ( sK2 != sK3
    | spl8_11 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl8_11
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f311,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f310])).

fof(f310,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_12 ),
    inference(superposition,[],[f58,f286])).

fof(f286,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl8_12 ),
    inference(resolution,[],[f245,f53])).

fof(f53,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f245,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_12
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f265,plain,
    ( ~ spl8_4
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f250,f117])).

fof(f117,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_4
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f250,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f54,f241])).

fof(f241,plain,
    ( sK2 = sK3
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f239])).

fof(f54,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f246,plain,
    ( spl8_11
    | spl8_12
    | ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f237,f106,f102,f243,f239])).

fof(f237,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f236,f192])).

fof(f236,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f235,f50])).

fof(f235,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | spl8_2 ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | spl8_2 ),
    inference(superposition,[],[f167,f198])).

fof(f167,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_1 ),
    inference(inner_rewriting,[],[f166])).

fof(f166,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f165,f96])).

fof(f165,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f163,f47])).

fof(f163,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f57,f162])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f161,plain,
    ( ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f157,f148])).

fof(f148,plain,
    ( r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f134,f138])).

fof(f138,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f137,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl8_2 ),
    inference(resolution,[],[f132,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f132,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f128,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f128,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f99,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f99,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f49,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f134,plain,
    ( r2_relset_1(sK0,k1_xboole_0,sK2,sK2)
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f117,f108])).

fof(f157,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f143,f153])).

fof(f153,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f152,f56])).

fof(f152,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f150,f63])).

fof(f150,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_2 ),
    inference(resolution,[],[f131,f67])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f124,f84])).

fof(f124,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f52,f108])).

fof(f143,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f125,f138])).

fof(f125,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f54,f108])).

fof(f120,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f113,f98])).

fof(f98,plain,(
    ~ sP7(sK1,sK0) ),
    inference(resolution,[],[f49,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP7(X1,X0) ) ),
    inference(general_splitting,[],[f81,f91_D])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f91_D])).

fof(f91_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP7(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f113,plain,
    ( sP7(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_3
  <=> sP7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f118,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f97,f115,f111])).

fof(f97,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP7(sK1,sK0) ),
    inference(resolution,[],[f49,f91])).

fof(f109,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f100,f106,f102])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f93,f48])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f49,f75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:12:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (17293)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.52  % (17292)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.53  % (17297)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.53  % (17307)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.21/0.53  % (17294)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.53  % (17298)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.54  % (17302)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.54  % (17311)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.54  % (17301)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (17303)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.54  % (17316)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.54  % (17291)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.54  % (17289)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (17300)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.54  % (17299)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.55  % (17304)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.55  % (17297)Refutation found. Thanks to Tanya!
% 1.37/0.55  % SZS status Theorem for theBenchmark
% 1.37/0.55  % SZS output start Proof for theBenchmark
% 1.37/0.55  fof(f320,plain,(
% 1.37/0.55    $false),
% 1.37/0.55    inference(avatar_sat_refutation,[],[f109,f118,f120,f161,f246,f265,f319])).
% 1.37/0.55  fof(f319,plain,(
% 1.37/0.55    ~spl8_1 | spl8_2 | spl8_11 | ~spl8_12),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f318])).
% 1.37/0.55  fof(f318,plain,(
% 1.37/0.55    $false | (~spl8_1 | spl8_2 | spl8_11 | ~spl8_12)),
% 1.37/0.55    inference(subsumption_resolution,[],[f317,f162])).
% 1.37/0.55  fof(f162,plain,(
% 1.37/0.55    sK0 = k1_relat_1(sK2) | ~spl8_1),
% 1.37/0.55    inference(backward_demodulation,[],[f95,f104])).
% 1.37/0.55  fof(f104,plain,(
% 1.37/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_1),
% 1.37/0.55    inference(avatar_component_clause,[],[f102])).
% 1.37/0.55  fof(f102,plain,(
% 1.37/0.55    spl8_1 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.37/0.55  fof(f95,plain,(
% 1.37/0.55    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.37/0.55    inference(resolution,[],[f49,f74])).
% 1.37/0.55  fof(f74,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f23])).
% 1.37/0.55  fof(f23,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(ennf_transformation,[],[f11])).
% 1.37/0.55  fof(f11,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.37/0.55  fof(f49,plain,(
% 1.37/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f30,plain,(
% 1.37/0.55    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f29,f28])).
% 1.37/0.55  % (17296)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.55  fof(f28,plain,(
% 1.37/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f29,plain,(
% 1.37/0.55    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f17,plain,(
% 1.37/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.37/0.55    inference(flattening,[],[f16])).
% 1.37/0.55  fof(f16,plain,(
% 1.37/0.55    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.37/0.55    inference(ennf_transformation,[],[f15])).
% 1.37/0.55  fof(f15,negated_conjecture,(
% 1.37/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.37/0.55    inference(negated_conjecture,[],[f14])).
% 1.37/0.55  fof(f14,conjecture,(
% 1.37/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 1.37/0.55  fof(f317,plain,(
% 1.37/0.55    sK0 != k1_relat_1(sK2) | (spl8_2 | spl8_11 | ~spl8_12)),
% 1.37/0.55    inference(forward_demodulation,[],[f316,f198])).
% 1.37/0.55  fof(f198,plain,(
% 1.37/0.55    sK0 = k1_relat_1(sK3) | spl8_2),
% 1.37/0.55    inference(forward_demodulation,[],[f191,f197])).
% 1.37/0.55  fof(f197,plain,(
% 1.37/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | spl8_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f196,f107])).
% 1.37/0.55  fof(f107,plain,(
% 1.37/0.55    k1_xboole_0 != sK1 | spl8_2),
% 1.37/0.55    inference(avatar_component_clause,[],[f106])).
% 1.37/0.55  fof(f106,plain,(
% 1.37/0.55    spl8_2 <=> k1_xboole_0 = sK1),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.37/0.55  fof(f196,plain,(
% 1.37/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.37/0.55    inference(subsumption_resolution,[],[f189,f51])).
% 1.37/0.55  fof(f51,plain,(
% 1.37/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f189,plain,(
% 1.37/0.55    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.37/0.55    inference(resolution,[],[f52,f75])).
% 1.37/0.55  fof(f75,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.37/0.55    inference(cnf_transformation,[],[f46])).
% 1.37/0.55  fof(f46,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(nnf_transformation,[],[f25])).
% 1.37/0.55  fof(f25,plain,(
% 1.37/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(flattening,[],[f24])).
% 1.37/0.55  fof(f24,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(ennf_transformation,[],[f13])).
% 1.37/0.55  fof(f13,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.37/0.55  fof(f52,plain,(
% 1.37/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f191,plain,(
% 1.37/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.37/0.55    inference(resolution,[],[f52,f74])).
% 1.37/0.55  fof(f316,plain,(
% 1.37/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | (spl8_11 | ~spl8_12)),
% 1.37/0.55    inference(subsumption_resolution,[],[f315,f192])).
% 1.37/0.55  fof(f192,plain,(
% 1.37/0.55    v1_relat_1(sK3)),
% 1.37/0.55    inference(resolution,[],[f52,f73])).
% 1.37/0.55  fof(f73,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f22])).
% 1.37/0.55  fof(f22,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(ennf_transformation,[],[f10])).
% 1.37/0.55  fof(f10,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.37/0.55  fof(f315,plain,(
% 1.37/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (spl8_11 | ~spl8_12)),
% 1.37/0.55    inference(subsumption_resolution,[],[f314,f50])).
% 1.37/0.55  fof(f50,plain,(
% 1.37/0.55    v1_funct_1(sK3)),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f314,plain,(
% 1.37/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl8_11 | ~spl8_12)),
% 1.37/0.55    inference(subsumption_resolution,[],[f313,f96])).
% 1.37/0.55  fof(f96,plain,(
% 1.37/0.55    v1_relat_1(sK2)),
% 1.37/0.55    inference(resolution,[],[f49,f73])).
% 1.37/0.55  fof(f313,plain,(
% 1.37/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl8_11 | ~spl8_12)),
% 1.37/0.55    inference(subsumption_resolution,[],[f312,f47])).
% 1.37/0.55  fof(f47,plain,(
% 1.37/0.55    v1_funct_1(sK2)),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f312,plain,(
% 1.37/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl8_11 | ~spl8_12)),
% 1.37/0.55    inference(subsumption_resolution,[],[f311,f240])).
% 1.37/0.55  fof(f240,plain,(
% 1.37/0.55    sK2 != sK3 | spl8_11),
% 1.37/0.55    inference(avatar_component_clause,[],[f239])).
% 1.37/0.55  fof(f239,plain,(
% 1.37/0.55    spl8_11 <=> sK2 = sK3),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.37/0.55  fof(f311,plain,(
% 1.37/0.55    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl8_12),
% 1.37/0.55    inference(trivial_inequality_removal,[],[f310])).
% 1.37/0.55  fof(f310,plain,(
% 1.37/0.55    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl8_12),
% 1.37/0.55    inference(superposition,[],[f58,f286])).
% 1.37/0.55  fof(f286,plain,(
% 1.37/0.55    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) | ~spl8_12),
% 1.37/0.55    inference(resolution,[],[f245,f53])).
% 1.37/0.55  fof(f53,plain,(
% 1.37/0.55    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f245,plain,(
% 1.37/0.55    r2_hidden(sK4(sK3,sK2),sK0) | ~spl8_12),
% 1.37/0.55    inference(avatar_component_clause,[],[f243])).
% 1.37/0.55  fof(f243,plain,(
% 1.37/0.55    spl8_12 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.37/0.55  fof(f58,plain,(
% 1.37/0.55    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f32])).
% 1.37/0.55  fof(f32,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f31])).
% 1.37/0.55  fof(f31,plain,(
% 1.37/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f19,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(flattening,[],[f18])).
% 1.37/0.55  fof(f18,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f9])).
% 1.37/0.55  fof(f9,axiom,(
% 1.37/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.37/0.55  fof(f265,plain,(
% 1.37/0.55    ~spl8_4 | ~spl8_11),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f264])).
% 1.37/0.55  fof(f264,plain,(
% 1.37/0.55    $false | (~spl8_4 | ~spl8_11)),
% 1.37/0.55    inference(subsumption_resolution,[],[f250,f117])).
% 1.37/0.55  fof(f117,plain,(
% 1.37/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl8_4),
% 1.37/0.55    inference(avatar_component_clause,[],[f115])).
% 1.37/0.55  fof(f115,plain,(
% 1.37/0.55    spl8_4 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.37/0.55  fof(f250,plain,(
% 1.37/0.55    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl8_11),
% 1.37/0.55    inference(backward_demodulation,[],[f54,f241])).
% 1.37/0.55  fof(f241,plain,(
% 1.37/0.55    sK2 = sK3 | ~spl8_11),
% 1.37/0.55    inference(avatar_component_clause,[],[f239])).
% 1.37/0.55  fof(f54,plain,(
% 1.37/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f246,plain,(
% 1.37/0.55    spl8_11 | spl8_12 | ~spl8_1 | spl8_2),
% 1.37/0.55    inference(avatar_split_clause,[],[f237,f106,f102,f243,f239])).
% 1.37/0.55  fof(f237,plain,(
% 1.37/0.55    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | (~spl8_1 | spl8_2)),
% 1.37/0.55    inference(subsumption_resolution,[],[f236,f192])).
% 1.37/0.55  fof(f236,plain,(
% 1.37/0.55    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl8_1 | spl8_2)),
% 1.37/0.55    inference(subsumption_resolution,[],[f235,f50])).
% 1.37/0.55  fof(f235,plain,(
% 1.37/0.55    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_1 | spl8_2)),
% 1.37/0.55    inference(trivial_inequality_removal,[],[f234])).
% 1.37/0.55  fof(f234,plain,(
% 1.37/0.55    sK0 != sK0 | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_1 | spl8_2)),
% 1.37/0.55    inference(superposition,[],[f167,f198])).
% 1.37/0.55  fof(f167,plain,(
% 1.37/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_1),
% 1.37/0.55    inference(inner_rewriting,[],[f166])).
% 1.37/0.55  fof(f166,plain,(
% 1.37/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_1),
% 1.37/0.55    inference(subsumption_resolution,[],[f165,f96])).
% 1.37/0.55  fof(f165,plain,(
% 1.37/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_1),
% 1.37/0.55    inference(subsumption_resolution,[],[f163,f47])).
% 1.37/0.55  fof(f163,plain,(
% 1.37/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_1),
% 1.37/0.55    inference(superposition,[],[f57,f162])).
% 1.37/0.55  fof(f57,plain,(
% 1.37/0.55    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f32])).
% 1.37/0.55  fof(f161,plain,(
% 1.37/0.55    ~spl8_2 | ~spl8_4),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f160])).
% 1.37/0.55  fof(f160,plain,(
% 1.37/0.55    $false | (~spl8_2 | ~spl8_4)),
% 1.37/0.55    inference(subsumption_resolution,[],[f157,f148])).
% 1.37/0.55  fof(f148,plain,(
% 1.37/0.55    r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_2 | ~spl8_4)),
% 1.37/0.55    inference(backward_demodulation,[],[f134,f138])).
% 1.37/0.55  fof(f138,plain,(
% 1.37/0.55    k1_xboole_0 = sK2 | ~spl8_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f137,f56])).
% 1.37/0.55  fof(f56,plain,(
% 1.37/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f5])).
% 1.37/0.55  fof(f5,axiom,(
% 1.37/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.37/0.55  fof(f137,plain,(
% 1.37/0.55    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl8_2),
% 1.37/0.55    inference(resolution,[],[f132,f63])).
% 1.37/0.55  fof(f63,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f38])).
% 1.37/0.55  fof(f38,plain,(
% 1.37/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.55    inference(flattening,[],[f37])).
% 1.37/0.55  fof(f37,plain,(
% 1.37/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.55    inference(nnf_transformation,[],[f4])).
% 1.37/0.55  fof(f4,axiom,(
% 1.37/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.55  fof(f132,plain,(
% 1.37/0.55    r1_tarski(sK2,k1_xboole_0) | ~spl8_2),
% 1.37/0.55    inference(forward_demodulation,[],[f128,f84])).
% 1.37/0.55  fof(f84,plain,(
% 1.37/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.37/0.55    inference(equality_resolution,[],[f71])).
% 1.37/0.55  fof(f71,plain,(
% 1.37/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.37/0.55    inference(cnf_transformation,[],[f45])).
% 1.37/0.55  fof(f45,plain,(
% 1.37/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.37/0.55    inference(flattening,[],[f44])).
% 1.37/0.55  fof(f44,plain,(
% 1.37/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.37/0.55    inference(nnf_transformation,[],[f7])).
% 1.37/0.55  fof(f7,axiom,(
% 1.37/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.37/0.55  fof(f128,plain,(
% 1.37/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl8_2),
% 1.37/0.55    inference(backward_demodulation,[],[f99,f108])).
% 1.37/0.55  fof(f108,plain,(
% 1.37/0.55    k1_xboole_0 = sK1 | ~spl8_2),
% 1.37/0.55    inference(avatar_component_clause,[],[f106])).
% 1.37/0.55  fof(f99,plain,(
% 1.37/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.37/0.55    inference(resolution,[],[f49,f67])).
% 1.37/0.55  fof(f67,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f43])).
% 1.37/0.55  fof(f43,plain,(
% 1.37/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.37/0.55    inference(nnf_transformation,[],[f8])).
% 1.37/0.55  fof(f8,axiom,(
% 1.37/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.37/0.55  fof(f134,plain,(
% 1.37/0.55    r2_relset_1(sK0,k1_xboole_0,sK2,sK2) | (~spl8_2 | ~spl8_4)),
% 1.37/0.55    inference(forward_demodulation,[],[f117,f108])).
% 1.37/0.55  fof(f157,plain,(
% 1.37/0.55    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl8_2),
% 1.37/0.55    inference(backward_demodulation,[],[f143,f153])).
% 1.37/0.55  fof(f153,plain,(
% 1.37/0.55    k1_xboole_0 = sK3 | ~spl8_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f152,f56])).
% 1.37/0.55  fof(f152,plain,(
% 1.37/0.55    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | ~spl8_2),
% 1.37/0.55    inference(resolution,[],[f150,f63])).
% 1.37/0.55  fof(f150,plain,(
% 1.37/0.55    r1_tarski(sK3,k1_xboole_0) | ~spl8_2),
% 1.37/0.55    inference(resolution,[],[f131,f67])).
% 1.37/0.55  fof(f131,plain,(
% 1.37/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl8_2),
% 1.37/0.55    inference(forward_demodulation,[],[f124,f84])).
% 1.37/0.55  fof(f124,plain,(
% 1.37/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_2),
% 1.37/0.55    inference(backward_demodulation,[],[f52,f108])).
% 1.37/0.55  fof(f143,plain,(
% 1.37/0.55    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,sK3) | ~spl8_2),
% 1.37/0.55    inference(backward_demodulation,[],[f125,f138])).
% 1.37/0.55  fof(f125,plain,(
% 1.37/0.55    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3) | ~spl8_2),
% 1.37/0.55    inference(backward_demodulation,[],[f54,f108])).
% 1.37/0.55  fof(f120,plain,(
% 1.37/0.55    ~spl8_3),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f119])).
% 1.37/0.55  fof(f119,plain,(
% 1.37/0.55    $false | ~spl8_3),
% 1.37/0.55    inference(subsumption_resolution,[],[f113,f98])).
% 1.37/0.55  fof(f98,plain,(
% 1.37/0.55    ~sP7(sK1,sK0)),
% 1.37/0.55    inference(resolution,[],[f49,f92])).
% 1.37/0.55  fof(f92,plain,(
% 1.37/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP7(X1,X0)) )),
% 1.37/0.55    inference(general_splitting,[],[f81,f91_D])).
% 1.37/0.55  fof(f91,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP7(X1,X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f91_D])).
% 1.37/0.55  fof(f91_D,plain,(
% 1.37/0.55    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP7(X1,X0)) )),
% 1.37/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.37/0.55  fof(f81,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f27])).
% 1.37/0.55  fof(f27,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(flattening,[],[f26])).
% 1.37/0.55  fof(f26,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.37/0.55    inference(ennf_transformation,[],[f12])).
% 1.37/0.55  fof(f12,axiom,(
% 1.37/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.37/0.55  fof(f113,plain,(
% 1.37/0.55    sP7(sK1,sK0) | ~spl8_3),
% 1.37/0.55    inference(avatar_component_clause,[],[f111])).
% 1.37/0.55  fof(f111,plain,(
% 1.37/0.55    spl8_3 <=> sP7(sK1,sK0)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.37/0.55  fof(f118,plain,(
% 1.37/0.55    spl8_3 | spl8_4),
% 1.37/0.55    inference(avatar_split_clause,[],[f97,f115,f111])).
% 1.37/0.55  fof(f97,plain,(
% 1.37/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | sP7(sK1,sK0)),
% 1.37/0.55    inference(resolution,[],[f49,f91])).
% 1.37/0.55  fof(f109,plain,(
% 1.37/0.55    spl8_1 | spl8_2),
% 1.37/0.55    inference(avatar_split_clause,[],[f100,f106,f102])).
% 1.37/0.55  fof(f100,plain,(
% 1.37/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.37/0.55    inference(subsumption_resolution,[],[f93,f48])).
% 1.37/0.55  fof(f48,plain,(
% 1.37/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f93,plain,(
% 1.37/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.37/0.55    inference(resolution,[],[f49,f75])).
% 1.37/0.55  % SZS output end Proof for theBenchmark
% 1.37/0.55  % (17297)------------------------------
% 1.37/0.55  % (17297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (17297)Termination reason: Refutation
% 1.37/0.55  
% 1.37/0.55  % (17297)Memory used [KB]: 10874
% 1.37/0.55  % (17297)Time elapsed: 0.135 s
% 1.37/0.55  % (17297)------------------------------
% 1.37/0.55  % (17297)------------------------------
% 1.37/0.55  % (17285)Success in time 0.186 s
%------------------------------------------------------------------------------
