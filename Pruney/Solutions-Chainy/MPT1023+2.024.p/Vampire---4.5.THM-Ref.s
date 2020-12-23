%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 434 expanded)
%              Number of leaves         :   27 ( 139 expanded)
%              Depth                    :   15
%              Number of atoms          :  528 (2558 expanded)
%              Number of equality atoms :  145 ( 446 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f496,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f136,f160,f166,f190,f195,f198,f257,f277,f353,f364,f495])).

fof(f495,plain,
    ( ~ spl6_11
    | spl6_16
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl6_11
    | spl6_16
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f491,f384])).

fof(f384,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ spl6_11
    | spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f371,f282])).

fof(f282,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl6_18
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f371,plain,
    ( sK0 != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ spl6_11
    | spl6_16 ),
    inference(subsumption_resolution,[],[f286,f251])).

fof(f251,plain,
    ( sK2 != sK3
    | spl6_16 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl6_16
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f286,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f285,f209])).

fof(f209,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_11 ),
    inference(superposition,[],[f144,f165])).

fof(f165,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl6_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f144,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f63,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
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
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f285,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f265,f120])).

fof(f120,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f265,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f178,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f178,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | k1_funct_1(X0,sK4(X0,sK2)) != k1_funct_1(sK2,sK4(X0,sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f176,f119])).

fof(f119,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f176,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(X0,sK2)) != k1_funct_1(sK2,sK4(X0,sK2))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f51,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f491,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ spl6_17 ),
    inference(resolution,[],[f487,f47])).

fof(f47,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f487,plain,
    ( m1_subset_1(sK4(sK3,sK2),sK0)
    | ~ spl6_17 ),
    inference(resolution,[],[f256,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f55,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
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

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f256,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl6_17
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f364,plain,
    ( ~ spl6_9
    | spl6_10
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl6_9
    | spl6_10
    | spl6_18 ),
    inference(global_subsumption,[],[f207,f283])).

fof(f283,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f281])).

fof(f207,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_9 ),
    inference(superposition,[],[f143,f155])).

fof(f155,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f143,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f63,f43])).

fof(f353,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(global_subsumption,[],[f336,f345])).

fof(f345,plain,
    ( r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f321,f303])).

fof(f303,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_5 ),
    inference(resolution,[],[f111,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f111,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_5
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f321,plain,
    ( r2_relset_1(sK0,k1_xboole_0,sK3,sK3)
    | ~ spl6_10 ),
    inference(superposition,[],[f140,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f140,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f81,f46])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f336,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f335,f296])).

fof(f296,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_4 ),
    inference(resolution,[],[f106,f114])).

fof(f106,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f335,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f316,f303])).

fof(f316,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3)
    | ~ spl6_10 ),
    inference(superposition,[],[f48,f159])).

fof(f48,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f277,plain,(
    ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f269,f139])).

fof(f139,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f81,f43])).

fof(f269,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_16 ),
    inference(superposition,[],[f48,f252])).

fof(f252,plain,
    ( sK2 = sK3
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f250])).

fof(f257,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f248,f163,f153,f254,f250])).

fof(f248,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f247,f209])).

fof(f247,plain,
    ( sK2 = sK3
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f246,f207])).

fof(f246,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f245,f209])).

fof(f245,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | sK2 = sK3
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f244,f120])).

fof(f244,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | sK2 = sK3
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f174,f44])).

fof(f174,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f172,f119])).

fof(f172,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f198,plain,
    ( spl6_5
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f196,f110])).

fof(f110,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f196,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f135,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f135,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_8
  <=> ! [X1] : ~ r2_hidden(X1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f195,plain,
    ( spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f193,f105])).

fof(f105,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f104])).

% (2144)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f193,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f127,f53])).

fof(f127,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_6
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f190,plain,
    ( spl6_7
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl6_7
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f188,f49])).

fof(f188,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f187,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f187,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl6_7
    | ~ spl6_10 ),
    inference(superposition,[],[f131,f159])).

fof(f131,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_7
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f166,plain,
    ( spl6_11
    | spl6_10 ),
    inference(avatar_split_clause,[],[f161,f157,f163])).

fof(f161,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f148,f45])).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f148,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f160,plain,
    ( spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f151,f157,f153])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f147,f42])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f147,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f64,f43])).

fof(f136,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f124,f129,f134])).

fof(f124,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f70,f46])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f132,plain,
    ( spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f123,f129,f126])).

fof(f123,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f70,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:42:14 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.46  % (2128)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.47  % (2136)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.48  % (2130)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.49  % (2120)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (2120)Refutation not found, incomplete strategy% (2120)------------------------------
% 0.19/0.49  % (2120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (2120)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (2120)Memory used [KB]: 10746
% 0.19/0.49  % (2120)Time elapsed: 0.099 s
% 0.19/0.49  % (2120)------------------------------
% 0.19/0.49  % (2120)------------------------------
% 0.19/0.49  % (2129)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.50  % (2119)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.50  % (2121)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.50  % (2135)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.50  % (2132)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (2126)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.50  % (2139)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.50  % (2126)Refutation not found, incomplete strategy% (2126)------------------------------
% 0.19/0.50  % (2126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (2126)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (2126)Memory used [KB]: 1663
% 0.19/0.50  % (2126)Time elapsed: 0.111 s
% 0.19/0.50  % (2126)------------------------------
% 0.19/0.50  % (2126)------------------------------
% 0.19/0.51  % (2133)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (2124)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.51  % (2131)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.51  % (2127)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.51  % (2123)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.51  % (2143)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.51  % (2140)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.51  % (2138)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.52  % (2134)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.52  % (2122)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.52  % (2129)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f496,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f132,f136,f160,f166,f190,f195,f198,f257,f277,f353,f364,f495])).
% 0.19/0.52  fof(f495,plain,(
% 0.19/0.52    ~spl6_11 | spl6_16 | ~spl6_17 | ~spl6_18),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f494])).
% 0.19/0.52  fof(f494,plain,(
% 0.19/0.52    $false | (~spl6_11 | spl6_16 | ~spl6_17 | ~spl6_18)),
% 0.19/0.52    inference(subsumption_resolution,[],[f491,f384])).
% 0.19/0.52  fof(f384,plain,(
% 0.19/0.52    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | (~spl6_11 | spl6_16 | ~spl6_18)),
% 0.19/0.52    inference(subsumption_resolution,[],[f371,f282])).
% 0.19/0.52  fof(f282,plain,(
% 0.19/0.52    sK0 = k1_relat_1(sK2) | ~spl6_18),
% 0.19/0.52    inference(avatar_component_clause,[],[f281])).
% 0.19/0.52  fof(f281,plain,(
% 0.19/0.52    spl6_18 <=> sK0 = k1_relat_1(sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.19/0.52  fof(f371,plain,(
% 0.19/0.52    sK0 != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | (~spl6_11 | spl6_16)),
% 0.19/0.52    inference(subsumption_resolution,[],[f286,f251])).
% 0.19/0.52  fof(f251,plain,(
% 0.19/0.52    sK2 != sK3 | spl6_16),
% 0.19/0.52    inference(avatar_component_clause,[],[f250])).
% 0.19/0.52  fof(f250,plain,(
% 0.19/0.52    spl6_16 <=> sK2 = sK3),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.19/0.52  fof(f286,plain,(
% 0.19/0.52    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~spl6_11),
% 0.19/0.52    inference(forward_demodulation,[],[f285,f209])).
% 0.19/0.52  fof(f209,plain,(
% 0.19/0.52    sK0 = k1_relat_1(sK3) | ~spl6_11),
% 0.19/0.52    inference(superposition,[],[f144,f165])).
% 0.19/0.52  fof(f165,plain,(
% 0.19/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_11),
% 0.19/0.52    inference(avatar_component_clause,[],[f163])).
% 0.19/0.52  fof(f163,plain,(
% 0.19/0.52    spl6_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.19/0.52  fof(f144,plain,(
% 0.19/0.52    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.19/0.52    inference(resolution,[],[f63,f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28,f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.52    inference(flattening,[],[f14])).
% 0.19/0.52  fof(f14,plain,(
% 0.19/0.52    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.52    inference(ennf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.19/0.52    inference(negated_conjecture,[],[f12])).
% 0.19/0.52  fof(f12,conjecture,(
% 0.19/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.52  fof(f285,plain,(
% 0.19/0.52    k1_relat_1(sK2) != k1_relat_1(sK3) | sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.19/0.52    inference(subsumption_resolution,[],[f265,f120])).
% 0.19/0.52  fof(f120,plain,(
% 0.19/0.52    v1_relat_1(sK3)),
% 0.19/0.52    inference(resolution,[],[f62,f46])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.52  fof(f265,plain,(
% 0.19/0.52    k1_relat_1(sK2) != k1_relat_1(sK3) | sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK3)),
% 0.19/0.52    inference(resolution,[],[f178,f44])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    v1_funct_1(sK3)),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f178,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | k1_funct_1(X0,sK4(X0,sK2)) != k1_funct_1(sK2,sK4(X0,sK2)) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f176,f119])).
% 0.19/0.52  fof(f119,plain,(
% 0.19/0.52    v1_relat_1(sK2)),
% 0.19/0.52    inference(resolution,[],[f62,f43])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f176,plain,(
% 0.19/0.52    ( ! [X0] : (k1_funct_1(X0,sK4(X0,sK2)) != k1_funct_1(sK2,sK4(X0,sK2)) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(resolution,[],[f51,f41])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    v1_funct_1(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(flattening,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.19/0.52  fof(f491,plain,(
% 0.19/0.52    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) | ~spl6_17),
% 0.19/0.52    inference(resolution,[],[f487,f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ( ! [X4] : (~m1_subset_1(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f487,plain,(
% 0.19/0.52    m1_subset_1(sK4(sK3,sK2),sK0) | ~spl6_17),
% 0.19/0.52    inference(resolution,[],[f256,f82])).
% 0.19/0.52  fof(f82,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f55,f52])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.52    inference(rectify,[],[f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.52    inference(nnf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.52    inference(nnf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.52  fof(f256,plain,(
% 0.19/0.52    r2_hidden(sK4(sK3,sK2),sK0) | ~spl6_17),
% 0.19/0.52    inference(avatar_component_clause,[],[f254])).
% 0.19/0.52  fof(f254,plain,(
% 0.19/0.52    spl6_17 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.19/0.52  fof(f364,plain,(
% 0.19/0.52    ~spl6_9 | spl6_10 | spl6_18),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f363])).
% 0.19/0.52  fof(f363,plain,(
% 0.19/0.52    $false | (~spl6_9 | spl6_10 | spl6_18)),
% 0.19/0.52    inference(global_subsumption,[],[f207,f283])).
% 0.19/0.52  fof(f283,plain,(
% 0.19/0.52    sK0 != k1_relat_1(sK2) | spl6_18),
% 0.19/0.52    inference(avatar_component_clause,[],[f281])).
% 0.19/0.52  fof(f207,plain,(
% 0.19/0.52    sK0 = k1_relat_1(sK2) | ~spl6_9),
% 0.19/0.52    inference(superposition,[],[f143,f155])).
% 0.19/0.52  fof(f155,plain,(
% 0.19/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_9),
% 0.19/0.52    inference(avatar_component_clause,[],[f153])).
% 0.19/0.52  fof(f153,plain,(
% 0.19/0.52    spl6_9 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.19/0.52  fof(f143,plain,(
% 0.19/0.52    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.19/0.52    inference(resolution,[],[f63,f43])).
% 0.19/0.52  fof(f353,plain,(
% 0.19/0.52    ~spl6_4 | ~spl6_5 | ~spl6_10),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f352])).
% 0.19/0.52  fof(f352,plain,(
% 0.19/0.52    $false | (~spl6_4 | ~spl6_5 | ~spl6_10)),
% 0.19/0.52    inference(global_subsumption,[],[f336,f345])).
% 0.19/0.52  fof(f345,plain,(
% 0.19/0.52    r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_5 | ~spl6_10)),
% 0.19/0.52    inference(forward_demodulation,[],[f321,f303])).
% 0.19/0.52  fof(f303,plain,(
% 0.19/0.52    k1_xboole_0 = sK3 | ~spl6_5),
% 0.19/0.52    inference(resolution,[],[f111,f114])).
% 0.19/0.52  fof(f114,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.52    inference(resolution,[],[f61,f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    v1_xboole_0(k1_xboole_0)),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    v1_xboole_0(k1_xboole_0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.19/0.52  fof(f111,plain,(
% 0.19/0.52    v1_xboole_0(sK3) | ~spl6_5),
% 0.19/0.52    inference(avatar_component_clause,[],[f109])).
% 0.19/0.52  fof(f109,plain,(
% 0.19/0.52    spl6_5 <=> v1_xboole_0(sK3)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.52  fof(f321,plain,(
% 0.19/0.52    r2_relset_1(sK0,k1_xboole_0,sK3,sK3) | ~spl6_10),
% 0.19/0.52    inference(superposition,[],[f140,f159])).
% 0.19/0.52  fof(f159,plain,(
% 0.19/0.52    k1_xboole_0 = sK1 | ~spl6_10),
% 0.19/0.52    inference(avatar_component_clause,[],[f157])).
% 0.19/0.52  fof(f157,plain,(
% 0.19/0.52    spl6_10 <=> k1_xboole_0 = sK1),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.19/0.52  fof(f140,plain,(
% 0.19/0.52    r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.19/0.52    inference(resolution,[],[f81,f46])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f80])).
% 0.19/0.52  fof(f80,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.52    inference(equality_resolution,[],[f72])).
% 0.19/0.52  fof(f72,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(nnf_transformation,[],[f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(flattening,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.52  fof(f336,plain,(
% 0.19/0.52    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_10)),
% 0.19/0.52    inference(forward_demodulation,[],[f335,f296])).
% 0.19/0.52  fof(f296,plain,(
% 0.19/0.52    k1_xboole_0 = sK2 | ~spl6_4),
% 0.19/0.52    inference(resolution,[],[f106,f114])).
% 0.19/0.52  fof(f106,plain,(
% 0.19/0.52    v1_xboole_0(sK2) | ~spl6_4),
% 0.19/0.52    inference(avatar_component_clause,[],[f104])).
% 0.19/0.52  fof(f104,plain,(
% 0.19/0.52    spl6_4 <=> v1_xboole_0(sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.52  fof(f335,plain,(
% 0.19/0.52    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) | (~spl6_5 | ~spl6_10)),
% 0.19/0.52    inference(forward_demodulation,[],[f316,f303])).
% 0.19/0.52  fof(f316,plain,(
% 0.19/0.52    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3) | ~spl6_10),
% 0.19/0.52    inference(superposition,[],[f48,f159])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f277,plain,(
% 0.19/0.52    ~spl6_16),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f276])).
% 0.19/0.52  fof(f276,plain,(
% 0.19/0.52    $false | ~spl6_16),
% 0.19/0.52    inference(subsumption_resolution,[],[f269,f139])).
% 0.19/0.52  fof(f139,plain,(
% 0.19/0.52    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.19/0.52    inference(resolution,[],[f81,f43])).
% 0.19/0.52  fof(f269,plain,(
% 0.19/0.52    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl6_16),
% 0.19/0.52    inference(superposition,[],[f48,f252])).
% 0.19/0.52  fof(f252,plain,(
% 0.19/0.52    sK2 = sK3 | ~spl6_16),
% 0.19/0.52    inference(avatar_component_clause,[],[f250])).
% 0.19/0.52  fof(f257,plain,(
% 0.19/0.52    spl6_16 | spl6_17 | ~spl6_9 | ~spl6_11),
% 0.19/0.52    inference(avatar_split_clause,[],[f248,f163,f153,f254,f250])).
% 0.19/0.52  fof(f248,plain,(
% 0.19/0.52    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | (~spl6_9 | ~spl6_11)),
% 0.19/0.52    inference(forward_demodulation,[],[f247,f209])).
% 0.19/0.52  fof(f247,plain,(
% 0.19/0.52    sK2 = sK3 | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | (~spl6_9 | ~spl6_11)),
% 0.19/0.52    inference(subsumption_resolution,[],[f246,f207])).
% 0.19/0.52  fof(f246,plain,(
% 0.19/0.52    sK0 != k1_relat_1(sK2) | sK2 = sK3 | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | ~spl6_11),
% 0.19/0.52    inference(forward_demodulation,[],[f245,f209])).
% 0.19/0.52  fof(f245,plain,(
% 0.19/0.52    k1_relat_1(sK2) != k1_relat_1(sK3) | sK2 = sK3 | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))),
% 0.19/0.52    inference(subsumption_resolution,[],[f244,f120])).
% 0.19/0.52  fof(f244,plain,(
% 0.19/0.52    k1_relat_1(sK2) != k1_relat_1(sK3) | sK2 = sK3 | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.19/0.52    inference(resolution,[],[f174,f44])).
% 0.19/0.52  fof(f174,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f172,f119])).
% 0.19/0.52  fof(f172,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(resolution,[],[f50,f41])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f31])).
% 0.19/0.52  fof(f198,plain,(
% 0.19/0.52    spl6_5 | ~spl6_8),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f197])).
% 0.19/0.52  fof(f197,plain,(
% 0.19/0.52    $false | (spl6_5 | ~spl6_8)),
% 0.19/0.52    inference(subsumption_resolution,[],[f196,f110])).
% 0.19/0.52  fof(f110,plain,(
% 0.19/0.52    ~v1_xboole_0(sK3) | spl6_5),
% 0.19/0.52    inference(avatar_component_clause,[],[f109])).
% 0.19/0.52  fof(f196,plain,(
% 0.19/0.52    v1_xboole_0(sK3) | ~spl6_8),
% 0.19/0.52    inference(resolution,[],[f135,f53])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f35])).
% 0.19/0.52  fof(f135,plain,(
% 0.19/0.52    ( ! [X1] : (~r2_hidden(X1,sK3)) ) | ~spl6_8),
% 0.19/0.52    inference(avatar_component_clause,[],[f134])).
% 0.19/0.52  fof(f134,plain,(
% 0.19/0.52    spl6_8 <=> ! [X1] : ~r2_hidden(X1,sK3)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.19/0.52  fof(f195,plain,(
% 0.19/0.52    spl6_4 | ~spl6_6),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f194])).
% 0.19/0.52  fof(f194,plain,(
% 0.19/0.52    $false | (spl6_4 | ~spl6_6)),
% 0.19/0.52    inference(subsumption_resolution,[],[f193,f105])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    ~v1_xboole_0(sK2) | spl6_4),
% 0.19/0.52    inference(avatar_component_clause,[],[f104])).
% 0.19/0.52  % (2144)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.52  fof(f193,plain,(
% 0.19/0.52    v1_xboole_0(sK2) | ~spl6_6),
% 0.19/0.52    inference(resolution,[],[f127,f53])).
% 0.19/0.52  fof(f127,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl6_6),
% 0.19/0.52    inference(avatar_component_clause,[],[f126])).
% 0.19/0.52  fof(f126,plain,(
% 0.19/0.52    spl6_6 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.19/0.52  fof(f190,plain,(
% 0.19/0.52    spl6_7 | ~spl6_10),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f189])).
% 0.19/0.52  fof(f189,plain,(
% 0.19/0.52    $false | (spl6_7 | ~spl6_10)),
% 0.19/0.52    inference(subsumption_resolution,[],[f188,f49])).
% 0.19/0.52  fof(f188,plain,(
% 0.19/0.52    ~v1_xboole_0(k1_xboole_0) | (spl6_7 | ~spl6_10)),
% 0.19/0.52    inference(forward_demodulation,[],[f187,f73])).
% 0.19/0.52  fof(f73,plain,(
% 0.19/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.52    inference(flattening,[],[f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.52    inference(nnf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.52  fof(f187,plain,(
% 0.19/0.52    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (spl6_7 | ~spl6_10)),
% 0.19/0.52    inference(superposition,[],[f131,f159])).
% 0.19/0.52  fof(f131,plain,(
% 0.19/0.52    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl6_7),
% 0.19/0.52    inference(avatar_component_clause,[],[f129])).
% 0.19/0.52  fof(f129,plain,(
% 0.19/0.52    spl6_7 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.19/0.52  fof(f166,plain,(
% 0.19/0.52    spl6_11 | spl6_10),
% 0.19/0.52    inference(avatar_split_clause,[],[f161,f157,f163])).
% 0.19/0.52  fof(f161,plain,(
% 0.19/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.19/0.52    inference(subsumption_resolution,[],[f148,f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    v1_funct_2(sK3,sK0,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f148,plain,(
% 0.19/0.52    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.19/0.52    inference(resolution,[],[f64,f46])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(nnf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(flattening,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.52  fof(f160,plain,(
% 0.19/0.52    spl6_9 | spl6_10),
% 0.19/0.52    inference(avatar_split_clause,[],[f151,f157,f153])).
% 0.19/0.52  fof(f151,plain,(
% 0.19/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.19/0.52    inference(subsumption_resolution,[],[f147,f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f147,plain,(
% 0.19/0.52    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.19/0.52    inference(resolution,[],[f64,f43])).
% 0.19/0.52  fof(f136,plain,(
% 0.19/0.52    spl6_8 | ~spl6_7),
% 0.19/0.52    inference(avatar_split_clause,[],[f124,f129,f134])).
% 0.19/0.52  fof(f124,plain,(
% 0.19/0.52    ( ! [X1] : (~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK3)) )),
% 0.19/0.52    inference(resolution,[],[f70,f46])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    spl6_6 | ~spl6_7),
% 0.19/0.52    inference(avatar_split_clause,[],[f123,f129,f126])).
% 0.19/0.52  fof(f123,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.19/0.52    inference(resolution,[],[f70,f43])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (2129)------------------------------
% 0.19/0.52  % (2129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2129)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (2129)Memory used [KB]: 10874
% 0.19/0.52  % (2129)Time elapsed: 0.109 s
% 0.19/0.52  % (2129)------------------------------
% 0.19/0.52  % (2129)------------------------------
% 0.19/0.52  % (2125)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.52  % (2141)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.53  % (2137)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.53  % (2118)Success in time 0.186 s
%------------------------------------------------------------------------------
