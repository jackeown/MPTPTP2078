%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:08 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 404 expanded)
%              Number of leaves         :   27 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :  518 (2285 expanded)
%              Number of equality atoms :   86 ( 159 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f289,f422,f446,f458,f510,f518,f526])).

fof(f526,plain,(
    ~ spl9_17 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f524,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f524,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f522,f214])).

fof(f214,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f210,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f63,f57])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f210,plain,(
    ! [X3] : r1_tarski(k2_relat_1(k1_xboole_0),X3) ),
    inference(resolution,[],[f204,f57])).

fof(f204,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | r1_tarski(k2_relat_1(X3),X5) ) ),
    inference(resolution,[],[f169,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f169,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k2_relat_1(X3),k1_zfmisc_1(X4))
      | ~ r1_tarski(X3,k2_zfmisc_1(X5,X4)) ) ),
    inference(resolution,[],[f164,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f68,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f522,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK4)
    | ~ spl9_17 ),
    inference(backward_demodulation,[],[f158,f505])).

fof(f505,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl9_17
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f158,plain,(
    ~ r1_tarski(k2_relat_1(sK7),sK4) ),
    inference(subsumption_resolution,[],[f157,f54])).

fof(f54,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
        | ~ m1_subset_1(X4,sK5) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f16,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                  | ~ m1_subset_1(X4,sK5) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
              & v1_funct_2(X3,sK5,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                | ~ m1_subset_1(X4,sK5) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
            & v1_funct_2(X3,sK5,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK5,sK6,X3),sK4)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4)
              | ~ m1_subset_1(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK5,sK6,X3),sK4)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4)
            | ~ m1_subset_1(X4,sK5) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X3,sK5,sK6)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
          | ~ m1_subset_1(X4,sK5) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f157,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(superposition,[],[f56,f67])).

fof(f56,plain,(
    ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f518,plain,
    ( ~ spl9_15
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | ~ spl9_15
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f516,f88])).

fof(f88,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

% (20844)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f516,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl9_15
    | ~ spl9_18 ),
    inference(backward_demodulation,[],[f475,f509])).

fof(f509,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl9_18
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f475,plain,
    ( sP0(sK5,k1_xboole_0)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f421,f459])).

fof(f459,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_15 ),
    inference(resolution,[],[f421,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f421,plain,
    ( sP0(sK5,sK6)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl9_15
  <=> sP0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f510,plain,
    ( spl9_17
    | spl9_18
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f501,f419,f507,f503])).

fof(f501,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f500,f461])).

fof(f461,plain,
    ( v1_funct_2(sK7,sK5,k1_xboole_0)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f53,f459])).

fof(f53,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f500,plain,
    ( ~ v1_funct_2(sK7,sK5,k1_xboole_0)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl9_15 ),
    inference(resolution,[],[f468,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f468,plain,
    ( sP2(sK7,k1_xboole_0,sK5)
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f138,f459])).

fof(f138,plain,(
    sP2(sK7,sK6,sK5) ),
    inference(resolution,[],[f76,f54])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f23,f30,f29,f28])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f458,plain,
    ( ~ spl9_10
    | ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f455,f158])).

fof(f455,plain,
    ( r1_tarski(k2_relat_1(sK7),sK4)
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(resolution,[],[f448,f195])).

fof(f195,plain,(
    ! [X4,X5,X3] :
      ( ~ sP3(X3,X4,X5)
      | r1_tarski(k2_relat_1(X5),X3) ) ),
    inference(resolution,[],[f168,f64])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
      | ~ sP3(X1,X2,X0) ) ),
    inference(resolution,[],[f164,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f448,plain,
    ( sP3(sK4,sK5,sK7)
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f284,f417])).

fof(f417,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl9_14
  <=> sK5 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f284,plain,
    ( sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl9_10
  <=> sP3(sK4,k1_relat_1(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f446,plain,
    ( spl9_11
    | ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | spl9_11
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f439,f158])).

fof(f439,plain,
    ( r1_tarski(k2_relat_1(sK7),sK4)
    | spl9_11
    | ~ spl9_14 ),
    inference(resolution,[],[f432,f195])).

fof(f432,plain,
    ( sP3(sK4,sK5,sK7)
    | spl9_11
    | ~ spl9_14 ),
    inference(resolution,[],[f430,f423])).

fof(f423,plain,
    ( ~ r2_hidden(sK8(sK5,sK4,sK7),sK5)
    | spl9_11
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f290,f417])).

fof(f290,plain,
    ( ~ r2_hidden(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | spl9_11 ),
    inference(resolution,[],[f288,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f288,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl9_11
  <=> m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f430,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK5,X1,sK7),sK5)
        | sP3(X1,sK5,sK7) )
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f429,f97])).

fof(f97,plain,(
    v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f94,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f94,plain,
    ( v1_relat_1(sK7)
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(resolution,[],[f58,f54])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f429,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK5,X1,sK7),sK5)
        | sP3(X1,sK5,sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f426,f52])).

fof(f52,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f426,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK5,X1,sK7),sK5)
        | sP3(X1,sK5,sK7)
        | ~ v1_funct_1(sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl9_14 ),
    inference(superposition,[],[f90,f417])).

fof(f90,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP3(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | r2_hidden(sK8(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f25,f32])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f422,plain,
    ( spl9_14
    | spl9_15 ),
    inference(avatar_split_clause,[],[f413,f419,f415])).

fof(f413,plain,
    ( sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f411,f53])).

fof(f411,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(resolution,[],[f201,f54])).

fof(f201,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f199,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f199,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f71,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f289,plain,
    ( spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f280,f286,f282])).

fof(f280,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f279,f97])).

fof(f279,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f278,f52])).

fof(f278,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f277,f89])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1)
      | sP3(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f277,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5) ) ),
    inference(subsumption_resolution,[],[f276,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f276,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f275,f52])).

fof(f275,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f274,f53])).

fof(f274,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f273,f54])).

fof(f273,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(superposition,[],[f55,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f55,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (20832)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (20825)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (20838)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (20841)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (20833)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (20823)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (20834)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (20827)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (20824)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (20820)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (20830)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.25/0.52  % (20831)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.25/0.52  % (20825)Refutation not found, incomplete strategy% (20825)------------------------------
% 1.25/0.52  % (20825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (20825)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (20825)Memory used [KB]: 10618
% 1.25/0.52  % (20825)Time elapsed: 0.095 s
% 1.25/0.52  % (20825)------------------------------
% 1.25/0.52  % (20825)------------------------------
% 1.25/0.52  % (20837)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.25/0.52  % (20840)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.25/0.52  % (20822)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.25/0.53  % (20829)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.25/0.53  % (20823)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f528,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(avatar_sat_refutation,[],[f289,f422,f446,f458,f510,f518,f526])).
% 1.25/0.53  fof(f526,plain,(
% 1.25/0.53    ~spl9_17),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f525])).
% 1.25/0.53  fof(f525,plain,(
% 1.25/0.53    $false | ~spl9_17),
% 1.25/0.53    inference(subsumption_resolution,[],[f524,f57])).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.25/0.53  fof(f524,plain,(
% 1.25/0.53    ~r1_tarski(k1_xboole_0,sK4) | ~spl9_17),
% 1.25/0.53    inference(forward_demodulation,[],[f522,f214])).
% 1.25/0.53  fof(f214,plain,(
% 1.25/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.25/0.53    inference(resolution,[],[f210,f121])).
% 1.25/0.53  fof(f121,plain,(
% 1.25/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(resolution,[],[f63,f57])).
% 1.25/0.53  fof(f63,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f39])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.25/0.53    inference(flattening,[],[f38])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.25/0.53    inference(nnf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.25/0.53  fof(f210,plain,(
% 1.25/0.53    ( ! [X3] : (r1_tarski(k2_relat_1(k1_xboole_0),X3)) )),
% 1.25/0.53    inference(resolution,[],[f204,f57])).
% 1.25/0.53  fof(f204,plain,(
% 1.25/0.53    ( ! [X4,X5,X3] : (~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | r1_tarski(k2_relat_1(X3),X5)) )),
% 1.25/0.53    inference(resolution,[],[f169,f64])).
% 1.25/0.53  fof(f64,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f40])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.25/0.53    inference(nnf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.25/0.53  fof(f169,plain,(
% 1.25/0.53    ( ! [X4,X5,X3] : (m1_subset_1(k2_relat_1(X3),k1_zfmisc_1(X4)) | ~r1_tarski(X3,k2_zfmisc_1(X5,X4))) )),
% 1.25/0.53    inference(resolution,[],[f164,f65])).
% 1.25/0.53  fof(f65,plain,(
% 1.25/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f40])).
% 1.25/0.53  fof(f164,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 1.25/0.53    inference(duplicate_literal_removal,[],[f163])).
% 1.25/0.53  fof(f163,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.25/0.53    inference(superposition,[],[f68,f67])).
% 1.25/0.53  fof(f67,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.25/0.53  fof(f68,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.25/0.53  fof(f522,plain,(
% 1.25/0.53    ~r1_tarski(k2_relat_1(k1_xboole_0),sK4) | ~spl9_17),
% 1.25/0.53    inference(backward_demodulation,[],[f158,f505])).
% 1.25/0.53  fof(f505,plain,(
% 1.25/0.53    k1_xboole_0 = sK7 | ~spl9_17),
% 1.25/0.53    inference(avatar_component_clause,[],[f503])).
% 1.25/0.53  fof(f503,plain,(
% 1.25/0.53    spl9_17 <=> k1_xboole_0 = sK7),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.25/0.53  fof(f158,plain,(
% 1.25/0.53    ~r1_tarski(k2_relat_1(sK7),sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f157,f54])).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.25/0.53    inference(cnf_transformation,[],[f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ((~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)) & ~v1_xboole_0(sK5)),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f16,f36,f35,f34])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK5))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK5,sK6,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ? [X3] : (~r1_tarski(k2_relset_1(sK5,sK6,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.25/0.53    inference(flattening,[],[f15])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f14])).
% 1.25/0.53  fof(f14,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.25/0.53    inference(negated_conjecture,[],[f13])).
% 1.25/0.53  fof(f13,conjecture,(
% 1.25/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 1.25/0.53  fof(f157,plain,(
% 1.25/0.53    ~r1_tarski(k2_relat_1(sK7),sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.25/0.53    inference(superposition,[],[f56,f67])).
% 1.25/0.53  fof(f56,plain,(
% 1.25/0.53    ~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)),
% 1.25/0.53    inference(cnf_transformation,[],[f37])).
% 1.38/0.53  fof(f518,plain,(
% 1.38/0.53    ~spl9_15 | ~spl9_18),
% 1.38/0.53    inference(avatar_contradiction_clause,[],[f517])).
% 1.38/0.53  fof(f517,plain,(
% 1.38/0.53    $false | (~spl9_15 | ~spl9_18)),
% 1.38/0.53    inference(subsumption_resolution,[],[f516,f88])).
% 1.38/0.53  fof(f88,plain,(
% 1.38/0.53    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 1.38/0.53    inference(equality_resolution,[],[f74])).
% 1.38/0.53  fof(f74,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f45])).
% 1.38/0.53  fof(f45,plain,(
% 1.38/0.53    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.38/0.53    inference(nnf_transformation,[],[f28])).
% 1.38/0.53  % (20844)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.38/0.53  fof(f28,plain,(
% 1.38/0.53    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.38/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.38/0.53  fof(f516,plain,(
% 1.38/0.53    sP0(k1_xboole_0,k1_xboole_0) | (~spl9_15 | ~spl9_18)),
% 1.38/0.53    inference(backward_demodulation,[],[f475,f509])).
% 1.38/0.53  fof(f509,plain,(
% 1.38/0.53    k1_xboole_0 = sK5 | ~spl9_18),
% 1.38/0.53    inference(avatar_component_clause,[],[f507])).
% 1.38/0.53  fof(f507,plain,(
% 1.38/0.53    spl9_18 <=> k1_xboole_0 = sK5),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.38/0.53  fof(f475,plain,(
% 1.38/0.53    sP0(sK5,k1_xboole_0) | ~spl9_15),
% 1.38/0.53    inference(backward_demodulation,[],[f421,f459])).
% 1.38/0.53  fof(f459,plain,(
% 1.38/0.53    k1_xboole_0 = sK6 | ~spl9_15),
% 1.38/0.53    inference(resolution,[],[f421,f73])).
% 1.38/0.53  fof(f73,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 1.38/0.53    inference(cnf_transformation,[],[f45])).
% 1.38/0.53  fof(f421,plain,(
% 1.38/0.53    sP0(sK5,sK6) | ~spl9_15),
% 1.38/0.53    inference(avatar_component_clause,[],[f419])).
% 1.38/0.53  fof(f419,plain,(
% 1.38/0.53    spl9_15 <=> sP0(sK5,sK6)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.38/0.53  fof(f510,plain,(
% 1.38/0.53    spl9_17 | spl9_18 | ~spl9_15),
% 1.38/0.53    inference(avatar_split_clause,[],[f501,f419,f507,f503])).
% 1.38/0.53  fof(f501,plain,(
% 1.38/0.53    k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~spl9_15),
% 1.38/0.53    inference(subsumption_resolution,[],[f500,f461])).
% 1.38/0.53  fof(f461,plain,(
% 1.38/0.53    v1_funct_2(sK7,sK5,k1_xboole_0) | ~spl9_15),
% 1.38/0.53    inference(backward_demodulation,[],[f53,f459])).
% 1.38/0.53  fof(f53,plain,(
% 1.38/0.53    v1_funct_2(sK7,sK5,sK6)),
% 1.38/0.53    inference(cnf_transformation,[],[f37])).
% 1.38/0.53  fof(f500,plain,(
% 1.38/0.53    ~v1_funct_2(sK7,sK5,k1_xboole_0) | k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~spl9_15),
% 1.38/0.53    inference(resolution,[],[f468,f87])).
% 1.38/0.53  fof(f87,plain,(
% 1.38/0.53    ( ! [X2,X0] : (~sP2(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 1.38/0.53    inference(equality_resolution,[],[f69])).
% 1.38/0.53  fof(f69,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f42])).
% 1.38/0.53  fof(f42,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 1.38/0.53    inference(rectify,[],[f41])).
% 1.38/0.53  fof(f41,plain,(
% 1.38/0.53    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.38/0.53    inference(nnf_transformation,[],[f30])).
% 1.38/0.53  fof(f30,plain,(
% 1.38/0.53    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.38/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.38/0.53  fof(f468,plain,(
% 1.38/0.53    sP2(sK7,k1_xboole_0,sK5) | ~spl9_15),
% 1.38/0.53    inference(backward_demodulation,[],[f138,f459])).
% 1.38/0.53  fof(f138,plain,(
% 1.38/0.53    sP2(sK7,sK6,sK5)),
% 1.38/0.53    inference(resolution,[],[f76,f54])).
% 1.38/0.53  fof(f76,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f31])).
% 1.38/0.53  fof(f31,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.53    inference(definition_folding,[],[f23,f30,f29,f28])).
% 1.38/0.53  fof(f29,plain,(
% 1.38/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.38/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.38/0.53  fof(f23,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.53    inference(flattening,[],[f22])).
% 1.38/0.53  fof(f22,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.53    inference(ennf_transformation,[],[f10])).
% 1.38/0.53  fof(f10,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.38/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.38/0.53  fof(f458,plain,(
% 1.38/0.53    ~spl9_10 | ~spl9_14),
% 1.38/0.53    inference(avatar_contradiction_clause,[],[f457])).
% 1.38/0.53  fof(f457,plain,(
% 1.38/0.53    $false | (~spl9_10 | ~spl9_14)),
% 1.38/0.53    inference(subsumption_resolution,[],[f455,f158])).
% 1.38/0.53  fof(f455,plain,(
% 1.38/0.53    r1_tarski(k2_relat_1(sK7),sK4) | (~spl9_10 | ~spl9_14)),
% 1.38/0.53    inference(resolution,[],[f448,f195])).
% 1.38/0.53  fof(f195,plain,(
% 1.38/0.53    ( ! [X4,X5,X3] : (~sP3(X3,X4,X5) | r1_tarski(k2_relat_1(X5),X3)) )),
% 1.38/0.53    inference(resolution,[],[f168,f64])).
% 1.38/0.53  fof(f168,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1)) | ~sP3(X1,X2,X0)) )),
% 1.38/0.53    inference(resolution,[],[f164,f79])).
% 1.38/0.53  fof(f79,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP3(X0,X1,X2)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f47])).
% 1.38/0.53  fof(f47,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP3(X0,X1,X2))),
% 1.38/0.53    inference(rectify,[],[f46])).
% 1.38/0.53  fof(f46,plain,(
% 1.38/0.53    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 1.38/0.53    inference(nnf_transformation,[],[f32])).
% 1.38/0.53  fof(f32,plain,(
% 1.38/0.53    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 1.38/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.38/0.53  fof(f448,plain,(
% 1.38/0.53    sP3(sK4,sK5,sK7) | (~spl9_10 | ~spl9_14)),
% 1.38/0.53    inference(forward_demodulation,[],[f284,f417])).
% 1.38/0.53  fof(f417,plain,(
% 1.38/0.53    sK5 = k1_relat_1(sK7) | ~spl9_14),
% 1.38/0.53    inference(avatar_component_clause,[],[f415])).
% 1.38/0.53  fof(f415,plain,(
% 1.38/0.53    spl9_14 <=> sK5 = k1_relat_1(sK7)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.38/0.53  fof(f284,plain,(
% 1.38/0.53    sP3(sK4,k1_relat_1(sK7),sK7) | ~spl9_10),
% 1.38/0.53    inference(avatar_component_clause,[],[f282])).
% 1.38/0.53  fof(f282,plain,(
% 1.38/0.53    spl9_10 <=> sP3(sK4,k1_relat_1(sK7),sK7)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.38/0.53  fof(f446,plain,(
% 1.38/0.53    spl9_11 | ~spl9_14),
% 1.38/0.53    inference(avatar_contradiction_clause,[],[f445])).
% 1.38/0.53  fof(f445,plain,(
% 1.38/0.53    $false | (spl9_11 | ~spl9_14)),
% 1.38/0.53    inference(subsumption_resolution,[],[f439,f158])).
% 1.38/0.53  fof(f439,plain,(
% 1.38/0.53    r1_tarski(k2_relat_1(sK7),sK4) | (spl9_11 | ~spl9_14)),
% 1.38/0.53    inference(resolution,[],[f432,f195])).
% 1.38/0.53  fof(f432,plain,(
% 1.38/0.53    sP3(sK4,sK5,sK7) | (spl9_11 | ~spl9_14)),
% 1.38/0.53    inference(resolution,[],[f430,f423])).
% 1.38/0.53  fof(f423,plain,(
% 1.38/0.53    ~r2_hidden(sK8(sK5,sK4,sK7),sK5) | (spl9_11 | ~spl9_14)),
% 1.38/0.53    inference(backward_demodulation,[],[f290,f417])).
% 1.38/0.53  fof(f290,plain,(
% 1.38/0.53    ~r2_hidden(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | spl9_11),
% 1.38/0.53    inference(resolution,[],[f288,f60])).
% 1.38/0.53  fof(f60,plain,(
% 1.38/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f18])).
% 1.38/0.53  fof(f18,plain,(
% 1.38/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f3])).
% 1.38/0.53  fof(f3,axiom,(
% 1.38/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.38/0.53  fof(f288,plain,(
% 1.38/0.53    ~m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | spl9_11),
% 1.38/0.53    inference(avatar_component_clause,[],[f286])).
% 1.38/0.53  fof(f286,plain,(
% 1.38/0.53    spl9_11 <=> m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.38/0.53  fof(f430,plain,(
% 1.38/0.53    ( ! [X1] : (r2_hidden(sK8(sK5,X1,sK7),sK5) | sP3(X1,sK5,sK7)) ) | ~spl9_14),
% 1.38/0.53    inference(subsumption_resolution,[],[f429,f97])).
% 1.38/0.53  fof(f97,plain,(
% 1.38/0.53    v1_relat_1(sK7)),
% 1.38/0.53    inference(subsumption_resolution,[],[f94,f59])).
% 1.38/0.53  fof(f59,plain,(
% 1.38/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f6])).
% 1.38/0.53  fof(f6,axiom,(
% 1.38/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.38/0.53  fof(f94,plain,(
% 1.38/0.53    v1_relat_1(sK7) | ~v1_relat_1(k2_zfmisc_1(sK5,sK6))),
% 1.38/0.53    inference(resolution,[],[f58,f54])).
% 1.38/0.53  fof(f58,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f17])).
% 1.38/0.53  fof(f17,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.53    inference(ennf_transformation,[],[f5])).
% 1.38/0.53  fof(f5,axiom,(
% 1.38/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.38/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.38/0.53  fof(f429,plain,(
% 1.38/0.53    ( ! [X1] : (r2_hidden(sK8(sK5,X1,sK7),sK5) | sP3(X1,sK5,sK7) | ~v1_relat_1(sK7)) ) | ~spl9_14),
% 1.38/0.53    inference(subsumption_resolution,[],[f426,f52])).
% 1.38/0.53  fof(f52,plain,(
% 1.38/0.53    v1_funct_1(sK7)),
% 1.38/0.53    inference(cnf_transformation,[],[f37])).
% 1.38/0.53  fof(f426,plain,(
% 1.38/0.53    ( ! [X1] : (r2_hidden(sK8(sK5,X1,sK7),sK5) | sP3(X1,sK5,sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) ) | ~spl9_14),
% 1.38/0.53    inference(superposition,[],[f90,f417])).
% 1.38/0.53  fof(f90,plain,(
% 1.38/0.53    ( ! [X2,X1] : (r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP3(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.53    inference(equality_resolution,[],[f80])).
% 1.38/0.53  fof(f80,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | r2_hidden(sK8(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f49])).
% 1.38/0.53  fof(f49,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (sP3(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f48])).
% 1.38/0.53  fof(f48,plain,(
% 1.38/0.53    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f33,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (sP3(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.53    inference(definition_folding,[],[f25,f32])).
% 1.38/0.53  fof(f25,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.53    inference(flattening,[],[f24])).
% 1.38/0.53  fof(f24,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.38/0.53    inference(ennf_transformation,[],[f12])).
% 1.38/0.53  fof(f12,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.38/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 1.38/0.53  fof(f422,plain,(
% 1.38/0.53    spl9_14 | spl9_15),
% 1.38/0.53    inference(avatar_split_clause,[],[f413,f419,f415])).
% 1.38/0.53  fof(f413,plain,(
% 1.38/0.53    sP0(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 1.38/0.53    inference(subsumption_resolution,[],[f411,f53])).
% 1.38/0.53  fof(f411,plain,(
% 1.38/0.53    ~v1_funct_2(sK7,sK5,sK6) | sP0(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 1.38/0.53    inference(resolution,[],[f201,f54])).
% 1.38/0.53  fof(f201,plain,(
% 1.38/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.38/0.53    inference(subsumption_resolution,[],[f199,f75])).
% 1.38/0.53  fof(f75,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f31])).
% 1.38/0.53  fof(f199,plain,(
% 1.38/0.53    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.38/0.53    inference(superposition,[],[f71,f66])).
% 1.38/0.53  fof(f66,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f19])).
% 1.38/0.53  fof(f19,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.53    inference(ennf_transformation,[],[f8])).
% 1.38/0.53  fof(f8,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.38/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.38/0.53  fof(f71,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f44])).
% 1.38/0.53  fof(f44,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.38/0.53    inference(rectify,[],[f43])).
% 1.38/0.53  fof(f43,plain,(
% 1.38/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.38/0.53    inference(nnf_transformation,[],[f29])).
% 1.38/0.53  fof(f289,plain,(
% 1.38/0.53    spl9_10 | ~spl9_11),
% 1.38/0.53    inference(avatar_split_clause,[],[f280,f286,f282])).
% 1.38/0.53  fof(f280,plain,(
% 1.38/0.53    ~m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7)),
% 1.38/0.53    inference(subsumption_resolution,[],[f279,f97])).
% 1.38/0.53  fof(f279,plain,(
% 1.38/0.53    ~m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7) | ~v1_relat_1(sK7)),
% 1.38/0.53    inference(subsumption_resolution,[],[f278,f52])).
% 1.38/0.53  fof(f278,plain,(
% 1.38/0.53    ~m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 1.38/0.53    inference(resolution,[],[f277,f89])).
% 1.38/0.53  fof(f89,plain,(
% 1.38/0.53    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1) | sP3(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.53    inference(equality_resolution,[],[f81])).
% 1.38/0.53  fof(f81,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f49])).
% 1.38/0.53  fof(f277,plain,(
% 1.38/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5)) )),
% 1.38/0.53    inference(subsumption_resolution,[],[f276,f50])).
% 1.38/0.53  fof(f50,plain,(
% 1.38/0.53    ~v1_xboole_0(sK5)),
% 1.38/0.53    inference(cnf_transformation,[],[f37])).
% 1.38/0.53  fof(f276,plain,(
% 1.38/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | v1_xboole_0(sK5)) )),
% 1.38/0.53    inference(subsumption_resolution,[],[f275,f52])).
% 1.38/0.53  fof(f275,plain,(
% 1.38/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 1.38/0.53    inference(subsumption_resolution,[],[f274,f53])).
% 1.38/0.53  fof(f274,plain,(
% 1.38/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 1.38/0.53    inference(subsumption_resolution,[],[f273,f54])).
% 1.38/0.53  fof(f273,plain,(
% 1.38/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 1.38/0.53    inference(duplicate_literal_removal,[],[f272])).
% 1.38/0.53  fof(f272,plain,(
% 1.38/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 1.38/0.53    inference(superposition,[],[f55,f82])).
% 1.38/0.53  fof(f82,plain,(
% 1.38/0.53    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f27])).
% 1.38/0.53  fof(f27,plain,(
% 1.38/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.38/0.53    inference(flattening,[],[f26])).
% 1.38/0.53  fof(f26,plain,(
% 1.38/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.38/0.53    inference(ennf_transformation,[],[f11])).
% 1.38/0.53  fof(f11,axiom,(
% 1.38/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.38/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.38/0.53  fof(f55,plain,(
% 1.38/0.53    ( ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f37])).
% 1.38/0.53  % SZS output end Proof for theBenchmark
% 1.38/0.53  % (20823)------------------------------
% 1.38/0.53  % (20823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (20823)Termination reason: Refutation
% 1.38/0.53  
% 1.38/0.53  % (20823)Memory used [KB]: 6396
% 1.38/0.53  % (20823)Time elapsed: 0.109 s
% 1.38/0.53  % (20823)------------------------------
% 1.38/0.53  % (20823)------------------------------
% 1.38/0.53  % (20821)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.38/0.53  % (20813)Success in time 0.175 s
%------------------------------------------------------------------------------
