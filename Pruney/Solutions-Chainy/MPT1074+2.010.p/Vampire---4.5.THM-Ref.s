%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:06 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 426 expanded)
%              Number of leaves         :   28 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  553 (2652 expanded)
%              Number of equality atoms :   63 ( 244 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f412,f433,f434,f464,f564,f566,f581,f582,f585])).

fof(f585,plain,
    ( spl12_2
    | ~ spl12_15 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl12_2
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f583,f64])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f583,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl12_2
    | ~ spl12_15 ),
    inference(backward_demodulation,[],[f110,f570])).

fof(f570,plain,
    ( k1_xboole_0 = sK3
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl12_15
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f110,plain,
    ( ~ v1_xboole_0(sK3)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl12_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f582,plain,(
    ~ spl12_17 ),
    inference(avatar_split_clause,[],[f146,f578])).

fof(f578,plain,
    ( spl12_17
  <=> r1_tarski(k2_relat_1(sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f146,plain,(
    ~ r1_tarski(k2_relat_1(sK6),sK3) ),
    inference(subsumption_resolution,[],[f145,f61])).

fof(f61,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k2_relset_1(sK4,sK5,sK6),sK3)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK4,sK5,sK6,X4),sK3)
        | ~ m1_subset_1(X4,sK4) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6)
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f34,f33,f32])).

fof(f32,plain,
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
              ( ~ r1_tarski(k2_relset_1(sK4,X2,X3),sK3)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK4,X2,X3,X4),sK3)
                  | ~ m1_subset_1(X4,sK4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X2)))
              & v1_funct_2(X3,sK4,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK4,X2,X3),sK3)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK4,X2,X3,X4),sK3)
                | ~ m1_subset_1(X4,sK4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X2)))
            & v1_funct_2(X3,sK4,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK4,sK5,X3),sK3)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK4,sK5,X3,X4),sK3)
              | ~ m1_subset_1(X4,sK4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X3,sK4,sK5)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK4,sK5,X3),sK3)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK4,sK5,X3,X4),sK3)
            | ~ m1_subset_1(X4,sK4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
        & v1_funct_2(X3,sK4,sK5)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK4,sK5,sK6),sK3)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK4,sK5,sK6,X4),sK3)
          | ~ m1_subset_1(X4,sK4) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f145,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f63,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f63,plain,(
    ~ r1_tarski(k2_relset_1(sK4,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f581,plain,
    ( spl12_17
    | spl12_15
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f537,f409,f568,f578])).

fof(f409,plain,
    ( spl12_12
  <=> sP0(sK3,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f537,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(k2_relat_1(sK6),sK3)
    | ~ spl12_12 ),
    inference(resolution,[],[f529,f411])).

fof(f411,plain,
    ( sP0(sK3,sK4,sK6)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f409])).

fof(f529,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_xboole_0 = X0
      | r1_tarski(k2_relat_1(X2),X0) ) ),
    inference(resolution,[],[f522,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r1_tarski(k2_relat_1(X2),X0) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),X0)
      | ~ sP1(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f90,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sK11(X0,X1,X2) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ( r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0)
          & k1_relat_1(sK11(X0,X1,X2)) = X1
          & sK11(X0,X1,X2) = X2
          & v1_funct_1(sK11(X0,X1,X2))
          & v1_relat_1(sK11(X0,X1,X2)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X0)
          & k1_relat_1(X4) = X1
          & X2 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0)
        & k1_relat_1(sK11(X0,X1,X2)) = X1
        & sK11(X0,X1,X2) = X2
        & v1_funct_1(sK11(X0,X1,X2))
        & v1_relat_1(sK11(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X0)
            & k1_relat_1(X4) = X1
            & X2 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0,X3] :
      ( ( sP1(X1,X0,X3)
        | ! [X4] :
            ( ~ r1_tarski(k2_relat_1(X4),X1)
            | k1_relat_1(X4) != X0
            | X3 != X4
            | ~ v1_funct_1(X4)
            | ~ v1_relat_1(X4) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X1)
            & k1_relat_1(X4) = X0
            & X3 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP1(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X3] :
      ( sP1(X1,X0,X3)
    <=> ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X1)
          & k1_relat_1(X4) = X0
          & X3 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f522,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ sP0(X0,X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f325,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
      | sP1(X2,X1,X0) ) ),
    inference(resolution,[],[f82,f102])).

fof(f102,plain,(
    ! [X0,X1] : sP2(X0,X1,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f7,f30,f29])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,X0,sK10(X0,X1,X2))
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP1(X1,X0,sK10(X0,X1,X2))
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X0,X4) )
            & ( sP1(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,X0,sK10(X0,X1,X2))
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP1(X1,X0,sK10(X0,X1,X2))
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X0,X4) )
            & ( sP1(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X0,X3) )
            & ( sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X2,X0))
      | k1_xboole_0 = X0
      | ~ sP0(X0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f324,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v1_funct_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(X1,k1_funct_2(X2,X0))
      | ~ v1_funct_2(X1,X2,X0)
      | ~ sP0(X0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f311,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(X1,k1_funct_2(X2,X0))
      | ~ v1_funct_2(X1,X2,X0)
      | ~ v1_funct_1(X1)
      | ~ sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f78,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(X2,k1_funct_2(X0,X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(f566,plain,
    ( ~ spl12_2
    | spl12_1 ),
    inference(avatar_split_clause,[],[f472,f105,f108])).

fof(f105,plain,
    ( spl12_1
  <=> ! [X0] : ~ m1_subset_1(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f472,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK4)
      | ~ v1_xboole_0(sK3) ) ),
    inference(resolution,[],[f62,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f62,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK4,sK5,sK6,X4),sK3)
      | ~ m1_subset_1(X4,sK4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f564,plain,(
    ~ spl12_1 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f561,f57])).

fof(f57,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f561,plain,
    ( v1_xboole_0(sK4)
    | ~ spl12_1 ),
    inference(resolution,[],[f559,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f559,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl12_1 ),
    inference(resolution,[],[f106,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f106,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f464,plain,
    ( spl12_5
    | spl12_6 ),
    inference(avatar_split_clause,[],[f463,f320,f316])).

fof(f316,plain,
    ( spl12_5
  <=> r2_hidden(sK6,k1_funct_2(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f320,plain,
    ( spl12_6
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f463,plain,
    ( r2_hidden(sK6,k1_funct_2(sK4,sK5))
    | spl12_6 ),
    inference(subsumption_resolution,[],[f462,f59])).

fof(f59,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f462,plain,
    ( r2_hidden(sK6,k1_funct_2(sK4,sK5))
    | ~ v1_funct_1(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f461,f60])).

fof(f60,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f461,plain,
    ( r2_hidden(sK6,k1_funct_2(sK4,sK5))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f456,f321])).

fof(f321,plain,
    ( k1_xboole_0 != sK5
    | spl12_6 ),
    inference(avatar_component_clause,[],[f320])).

fof(f456,plain,
    ( k1_xboole_0 = sK5
    | r2_hidden(sK6,k1_funct_2(sK4,sK5))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(resolution,[],[f61,f78])).

fof(f434,plain,
    ( spl12_12
    | ~ spl12_5
    | spl12_11 ),
    inference(avatar_split_clause,[],[f414,f405,f316,f409])).

fof(f405,plain,
    ( spl12_11
  <=> m1_subset_1(sK8(sK4,sK3,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f414,plain,
    ( sP0(sK3,sK4,sK6)
    | ~ spl12_5
    | spl12_11 ),
    inference(resolution,[],[f413,f351])).

fof(f351,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK4,X1,sK6),sK4)
        | sP0(X1,sK4,sK6) )
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f350,f113])).

fof(f113,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f71,f61])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f350,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK4,X1,sK6),sK4)
        | sP0(X1,sK4,sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f345,f59])).

fof(f345,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK4,X1,sK6),sK4)
        | sP0(X1,sK4,sK6)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl12_5 ),
    inference(superposition,[],[f98,f330])).

fof(f330,plain,
    ( sK4 = k1_relat_1(sK6)
    | ~ spl12_5 ),
    inference(resolution,[],[f326,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | k1_relat_1(X2) = X1 ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = X1
      | ~ sP1(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f89,f88])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(sK11(X0,X1,X2)) = X1
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f326,plain,
    ( sP1(sK5,sK4,sK6)
    | ~ spl12_5 ),
    inference(resolution,[],[f318,f124])).

fof(f318,plain,
    ( r2_hidden(sK6,k1_funct_2(sK4,sK5))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f316])).

fof(f98,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP0(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | r2_hidden(sK8(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP0(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f28,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP0(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f20,f27])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f413,plain,
    ( ~ r2_hidden(sK8(sK4,sK3,sK6),sK4)
    | spl12_11 ),
    inference(resolution,[],[f407,f67])).

fof(f407,plain,
    ( ~ m1_subset_1(sK8(sK4,sK3,sK6),sK4)
    | spl12_11 ),
    inference(avatar_component_clause,[],[f405])).

fof(f433,plain,(
    ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f425,f64])).

fof(f425,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_6 ),
    inference(backward_demodulation,[],[f58,f322])).

fof(f322,plain,
    ( k1_xboole_0 = sK5
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f320])).

fof(f58,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f412,plain,
    ( ~ spl12_11
    | spl12_12
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f403,f316,f409,f405])).

fof(f403,plain,
    ( sP0(sK3,sK4,sK6)
    | ~ m1_subset_1(sK8(sK4,sK3,sK6),sK4)
    | ~ spl12_5 ),
    inference(forward_demodulation,[],[f402,f330])).

fof(f402,plain,
    ( ~ m1_subset_1(sK8(sK4,sK3,sK6),sK4)
    | sP0(sK3,k1_relat_1(sK6),sK6)
    | ~ spl12_5 ),
    inference(forward_demodulation,[],[f401,f330])).

fof(f401,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK6),sK3,sK6),sK4)
    | sP0(sK3,k1_relat_1(sK6),sK6) ),
    inference(subsumption_resolution,[],[f400,f113])).

fof(f400,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK6),sK3,sK6),sK4)
    | sP0(sK3,k1_relat_1(sK6),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f398,f59])).

fof(f398,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK6),sK3,sK6),sK4)
    | sP0(sK3,k1_relat_1(sK6),sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f397,f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1)
      | sP0(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f397,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK6,X0),sK3)
      | ~ m1_subset_1(X0,sK4) ) ),
    inference(subsumption_resolution,[],[f396,f57])).

fof(f396,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK6,X0),sK3)
      | ~ m1_subset_1(X0,sK4)
      | v1_xboole_0(sK4) ) ),
    inference(subsumption_resolution,[],[f395,f59])).

fof(f395,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK6,X0),sK3)
      | ~ m1_subset_1(X0,sK4)
      | ~ v1_funct_1(sK6)
      | v1_xboole_0(sK4) ) ),
    inference(subsumption_resolution,[],[f394,f60])).

fof(f394,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK6,X0),sK3)
      | ~ m1_subset_1(X0,sK4)
      | ~ v1_funct_2(sK6,sK4,sK5)
      | ~ v1_funct_1(sK6)
      | v1_xboole_0(sK4) ) ),
    inference(subsumption_resolution,[],[f393,f61])).

fof(f393,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK6,X0),sK3)
      | ~ m1_subset_1(X0,sK4)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ v1_funct_2(sK6,sK4,sK5)
      | ~ v1_funct_1(sK6)
      | v1_xboole_0(sK4) ) ),
    inference(duplicate_literal_removal,[],[f392])).

fof(f392,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK6,X0),sK3)
      | ~ m1_subset_1(X0,sK4)
      | ~ m1_subset_1(X0,sK4)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ v1_funct_2(sK6,sK4,sK5)
      | ~ v1_funct_1(sK6)
      | v1_xboole_0(sK4) ) ),
    inference(superposition,[],[f62,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (27813)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (27794)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (27796)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (27805)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (27792)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (27792)Refutation not found, incomplete strategy% (27792)------------------------------
% 0.20/0.50  % (27792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27792)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27792)Memory used [KB]: 10618
% 0.20/0.50  % (27792)Time elapsed: 0.092 s
% 0.20/0.50  % (27792)------------------------------
% 0.20/0.50  % (27792)------------------------------
% 0.20/0.50  % (27797)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (27803)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (27801)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (27799)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (27807)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (27809)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (27808)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (27800)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (27802)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (27816)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (27793)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (27804)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (27793)Refutation not found, incomplete strategy% (27793)------------------------------
% 0.20/0.52  % (27793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27793)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27793)Memory used [KB]: 10618
% 0.20/0.52  % (27793)Time elapsed: 0.116 s
% 0.20/0.52  % (27793)------------------------------
% 0.20/0.52  % (27793)------------------------------
% 0.20/0.52  % (27812)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (27810)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (27806)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (27795)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (27803)Refutation not found, incomplete strategy% (27803)------------------------------
% 0.20/0.53  % (27803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27803)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27803)Memory used [KB]: 10746
% 0.20/0.53  % (27803)Time elapsed: 0.119 s
% 0.20/0.53  % (27803)------------------------------
% 0.20/0.53  % (27803)------------------------------
% 0.20/0.53  % (27798)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (27805)Refutation not found, incomplete strategy% (27805)------------------------------
% 0.20/0.53  % (27805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27798)Refutation not found, incomplete strategy% (27798)------------------------------
% 0.20/0.53  % (27798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27798)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27798)Memory used [KB]: 10618
% 0.20/0.53  % (27798)Time elapsed: 0.097 s
% 0.20/0.53  % (27798)------------------------------
% 0.20/0.53  % (27798)------------------------------
% 0.20/0.53  % (27815)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (27814)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (27811)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (27805)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27805)Memory used [KB]: 6908
% 0.20/0.54  % (27805)Time elapsed: 0.106 s
% 0.20/0.54  % (27805)------------------------------
% 0.20/0.54  % (27805)------------------------------
% 1.52/0.54  % (27817)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.52/0.54  % (27796)Refutation found. Thanks to Tanya!
% 1.52/0.54  % SZS status Theorem for theBenchmark
% 1.52/0.54  % SZS output start Proof for theBenchmark
% 1.52/0.54  fof(f586,plain,(
% 1.52/0.54    $false),
% 1.52/0.54    inference(avatar_sat_refutation,[],[f412,f433,f434,f464,f564,f566,f581,f582,f585])).
% 1.52/0.54  fof(f585,plain,(
% 1.52/0.54    spl12_2 | ~spl12_15),
% 1.52/0.54    inference(avatar_contradiction_clause,[],[f584])).
% 1.52/0.54  fof(f584,plain,(
% 1.52/0.54    $false | (spl12_2 | ~spl12_15)),
% 1.52/0.54    inference(subsumption_resolution,[],[f583,f64])).
% 1.52/0.54  fof(f64,plain,(
% 1.52/0.54    v1_xboole_0(k1_xboole_0)),
% 1.52/0.54    inference(cnf_transformation,[],[f2])).
% 1.52/0.54  fof(f2,axiom,(
% 1.52/0.54    v1_xboole_0(k1_xboole_0)),
% 1.52/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.52/0.54  fof(f583,plain,(
% 1.52/0.54    ~v1_xboole_0(k1_xboole_0) | (spl12_2 | ~spl12_15)),
% 1.52/0.54    inference(backward_demodulation,[],[f110,f570])).
% 1.52/0.54  fof(f570,plain,(
% 1.52/0.54    k1_xboole_0 = sK3 | ~spl12_15),
% 1.52/0.54    inference(avatar_component_clause,[],[f568])).
% 1.52/0.54  fof(f568,plain,(
% 1.52/0.54    spl12_15 <=> k1_xboole_0 = sK3),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 1.52/0.54  fof(f110,plain,(
% 1.52/0.54    ~v1_xboole_0(sK3) | spl12_2),
% 1.52/0.54    inference(avatar_component_clause,[],[f108])).
% 1.52/0.54  fof(f108,plain,(
% 1.52/0.54    spl12_2 <=> v1_xboole_0(sK3)),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.52/0.54  fof(f582,plain,(
% 1.52/0.54    ~spl12_17),
% 1.52/0.54    inference(avatar_split_clause,[],[f146,f578])).
% 1.52/0.54  fof(f578,plain,(
% 1.52/0.54    spl12_17 <=> r1_tarski(k2_relat_1(sK6),sK3)),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).
% 1.52/0.54  fof(f146,plain,(
% 1.52/0.54    ~r1_tarski(k2_relat_1(sK6),sK3)),
% 1.52/0.54    inference(subsumption_resolution,[],[f145,f61])).
% 1.52/0.54  fof(f61,plain,(
% 1.52/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.52/0.54    inference(cnf_transformation,[],[f35])).
% 1.52/0.54  fof(f35,plain,(
% 1.52/0.54    ((~r1_tarski(k2_relset_1(sK4,sK5,sK6),sK3) & ! [X4] : (r2_hidden(k3_funct_2(sK4,sK5,sK6,X4),sK3) | ~m1_subset_1(X4,sK4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 1.52/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f34,f33,f32])).
% 1.52/0.54  fof(f32,plain,(
% 1.52/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK4,X2,X3),sK3) & ! [X4] : (r2_hidden(k3_funct_2(sK4,X2,X3,X4),sK3) | ~m1_subset_1(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X2))) & v1_funct_2(X3,sK4,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK4))),
% 1.52/0.54    introduced(choice_axiom,[])).
% 1.52/0.54  fof(f33,plain,(
% 1.52/0.54    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK4,X2,X3),sK3) & ! [X4] : (r2_hidden(k3_funct_2(sK4,X2,X3,X4),sK3) | ~m1_subset_1(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X2))) & v1_funct_2(X3,sK4,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK4,sK5,X3),sK3) & ! [X4] : (r2_hidden(k3_funct_2(sK4,sK5,X3,X4),sK3) | ~m1_subset_1(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) & ~v1_xboole_0(sK5))),
% 1.52/0.54    introduced(choice_axiom,[])).
% 1.52/0.54  fof(f34,plain,(
% 1.52/0.54    ? [X3] : (~r1_tarski(k2_relset_1(sK4,sK5,X3),sK3) & ! [X4] : (r2_hidden(k3_funct_2(sK4,sK5,X3,X4),sK3) | ~m1_subset_1(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK4,sK5,sK6),sK3) & ! [X4] : (r2_hidden(k3_funct_2(sK4,sK5,sK6,X4),sK3) | ~m1_subset_1(X4,sK4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 1.52/0.54    introduced(choice_axiom,[])).
% 1.52/0.54  fof(f15,plain,(
% 1.52/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.52/0.54    inference(flattening,[],[f14])).
% 1.52/0.54  fof(f14,plain,(
% 1.52/0.54    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.52/0.54    inference(ennf_transformation,[],[f13])).
% 1.52/0.54  fof(f13,negated_conjecture,(
% 1.52/0.54    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.52/0.54    inference(negated_conjecture,[],[f12])).
% 1.52/0.54  fof(f12,conjecture,(
% 1.52/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.52/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 1.52/0.54  fof(f145,plain,(
% 1.52/0.54    ~r1_tarski(k2_relat_1(sK6),sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.52/0.54    inference(superposition,[],[f63,f72])).
% 1.52/0.54  fof(f72,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.54    inference(cnf_transformation,[],[f18])).
% 1.52/0.54  fof(f18,plain,(
% 1.52/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.54    inference(ennf_transformation,[],[f6])).
% 1.52/0.54  fof(f6,axiom,(
% 1.52/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.52/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.52/0.54  fof(f63,plain,(
% 1.52/0.54    ~r1_tarski(k2_relset_1(sK4,sK5,sK6),sK3)),
% 1.52/0.54    inference(cnf_transformation,[],[f35])).
% 1.52/0.54  fof(f581,plain,(
% 1.52/0.54    spl12_17 | spl12_15 | ~spl12_12),
% 1.52/0.54    inference(avatar_split_clause,[],[f537,f409,f568,f578])).
% 1.52/0.54  fof(f409,plain,(
% 1.52/0.54    spl12_12 <=> sP0(sK3,sK4,sK6)),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 1.52/0.54  fof(f537,plain,(
% 1.52/0.54    k1_xboole_0 = sK3 | r1_tarski(k2_relat_1(sK6),sK3) | ~spl12_12),
% 1.52/0.54    inference(resolution,[],[f529,f411])).
% 1.52/0.54  fof(f411,plain,(
% 1.52/0.54    sP0(sK3,sK4,sK6) | ~spl12_12),
% 1.52/0.54    inference(avatar_component_clause,[],[f409])).
% 1.52/0.54  fof(f529,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_xboole_0 = X0 | r1_tarski(k2_relat_1(X2),X0)) )),
% 1.52/0.54    inference(resolution,[],[f522,f135])).
% 1.52/0.54  fof(f135,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r1_tarski(k2_relat_1(X2),X0)) )),
% 1.52/0.54    inference(duplicate_literal_removal,[],[f134])).
% 1.52/0.54  fof(f134,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),X0) | ~sP1(X0,X1,X2) | ~sP1(X0,X1,X2)) )),
% 1.52/0.54    inference(superposition,[],[f90,f88])).
% 1.52/0.54  fof(f88,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (sK11(X0,X1,X2) = X2 | ~sP1(X0,X1,X2)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f55])).
% 1.52/0.54  fof(f55,plain,(
% 1.52/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & ((r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0) & k1_relat_1(sK11(X0,X1,X2)) = X1 & sK11(X0,X1,X2) = X2 & v1_funct_1(sK11(X0,X1,X2)) & v1_relat_1(sK11(X0,X1,X2))) | ~sP1(X0,X1,X2)))),
% 1.52/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f53,f54])).
% 1.52/0.54  fof(f54,plain,(
% 1.52/0.54    ! [X2,X1,X0] : (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) => (r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0) & k1_relat_1(sK11(X0,X1,X2)) = X1 & sK11(X0,X1,X2) = X2 & v1_funct_1(sK11(X0,X1,X2)) & v1_relat_1(sK11(X0,X1,X2))))),
% 1.52/0.54    introduced(choice_axiom,[])).
% 1.52/0.54  fof(f53,plain,(
% 1.52/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP1(X0,X1,X2)))),
% 1.52/0.54    inference(rectify,[],[f52])).
% 1.52/0.54  fof(f52,plain,(
% 1.52/0.54    ! [X1,X0,X3] : ((sP1(X1,X0,X3) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP1(X1,X0,X3)))),
% 1.52/0.54    inference(nnf_transformation,[],[f29])).
% 1.52/0.54  fof(f29,plain,(
% 1.52/0.54    ! [X1,X0,X3] : (sP1(X1,X0,X3) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)))),
% 1.52/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.52/0.54  fof(f90,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0) | ~sP1(X0,X1,X2)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f55])).
% 1.52/0.54  fof(f522,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~sP0(X0,X1,X2) | k1_xboole_0 = X0) )),
% 1.52/0.54    inference(resolution,[],[f325,f124])).
% 1.52/0.54  fof(f124,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_funct_2(X1,X2)) | sP1(X2,X1,X0)) )),
% 1.52/0.54    inference(resolution,[],[f82,f102])).
% 1.52/0.54  fof(f102,plain,(
% 1.52/0.54    ( ! [X0,X1] : (sP2(X0,X1,k1_funct_2(X0,X1))) )),
% 1.52/0.54    inference(equality_resolution,[],[f92])).
% 1.52/0.54  fof(f92,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.52/0.54    inference(cnf_transformation,[],[f56])).
% 1.52/0.54  fof(f56,plain,(
% 1.52/0.54    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k1_funct_2(X0,X1) != X2))),
% 1.52/0.54    inference(nnf_transformation,[],[f31])).
% 1.52/0.54  fof(f31,plain,(
% 1.52/0.54    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 1.52/0.54    inference(definition_folding,[],[f7,f30,f29])).
% 1.52/0.54  fof(f30,plain,(
% 1.52/0.54    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X0,X3)))),
% 1.52/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.52/0.54  fof(f7,axiom,(
% 1.52/0.54    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 1.52/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 1.52/0.54  fof(f82,plain,(
% 1.52/0.54    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X1,X0,X4)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f51])).
% 1.52/0.54  fof(f51,plain,(
% 1.52/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,X0,sK10(X0,X1,X2)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP1(X1,X0,sK10(X0,X1,X2)) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X0,X4)) & (sP1(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.52/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f49,f50])).
% 1.52/0.54  fof(f50,plain,(
% 1.52/0.54    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2))) => ((~sP1(X1,X0,sK10(X0,X1,X2)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP1(X1,X0,sK10(X0,X1,X2)) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 1.52/0.54    introduced(choice_axiom,[])).
% 1.52/0.54  fof(f49,plain,(
% 1.52/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X0,X4)) & (sP1(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.52/0.54    inference(rectify,[],[f48])).
% 1.52/0.54  fof(f48,plain,(
% 1.52/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X0,X3)) & (sP1(X1,X0,X3) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 1.52/0.54    inference(nnf_transformation,[],[f30])).
% 1.52/0.54  fof(f325,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_funct_2(X2,X0)) | k1_xboole_0 = X0 | ~sP0(X0,X2,X1)) )),
% 1.52/0.54    inference(subsumption_resolution,[],[f324,f74])).
% 1.52/0.54  fof(f74,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v1_funct_2(X2,X1,X0)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f43])).
% 1.52/0.54  fof(f43,plain,(
% 1.52/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP0(X0,X1,X2))),
% 1.52/0.54    inference(rectify,[],[f42])).
% 1.52/0.54  fof(f42,plain,(
% 1.52/0.54    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP0(X1,X0,X2))),
% 1.52/0.54    inference(nnf_transformation,[],[f27])).
% 1.52/0.54  fof(f27,plain,(
% 1.52/0.54    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP0(X1,X0,X2))),
% 1.52/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/0.54  fof(f324,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | r2_hidden(X1,k1_funct_2(X2,X0)) | ~v1_funct_2(X1,X2,X0) | ~sP0(X0,X2,X1)) )),
% 1.52/0.54    inference(subsumption_resolution,[],[f311,f73])).
% 1.52/0.54  fof(f73,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v1_funct_1(X2)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f43])).
% 1.52/0.54  fof(f311,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | r2_hidden(X1,k1_funct_2(X2,X0)) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | ~sP0(X0,X2,X1)) )),
% 1.52/0.54    inference(resolution,[],[f78,f75])).
% 1.52/0.54  fof(f75,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP0(X0,X1,X2)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f43])).
% 1.52/0.54  fof(f78,plain,(
% 1.52/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(X2,k1_funct_2(X0,X1)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f22])).
% 1.52/0.54  fof(f22,plain,(
% 1.52/0.54    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.52/0.54    inference(flattening,[],[f21])).
% 1.52/0.54  fof(f21,plain,(
% 1.52/0.54    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.52/0.54    inference(ennf_transformation,[],[f9])).
% 1.52/0.54  fof(f9,axiom,(
% 1.52/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 1.52/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).
% 1.52/0.54  fof(f566,plain,(
% 1.52/0.54    ~spl12_2 | spl12_1),
% 1.52/0.54    inference(avatar_split_clause,[],[f472,f105,f108])).
% 1.52/0.54  fof(f105,plain,(
% 1.52/0.54    spl12_1 <=> ! [X0] : ~m1_subset_1(X0,sK4)),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.52/0.54  fof(f472,plain,(
% 1.52/0.54    ( ! [X0] : (~m1_subset_1(X0,sK4) | ~v1_xboole_0(sK3)) )),
% 1.52/0.54    inference(resolution,[],[f62,f65])).
% 1.52/0.54  fof(f65,plain,(
% 1.52/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f39])).
% 1.52/0.54  fof(f39,plain,(
% 1.52/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).
% 1.52/0.54  fof(f38,plain,(
% 1.52/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.52/0.54    introduced(choice_axiom,[])).
% 1.52/0.55  fof(f37,plain,(
% 1.52/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.55    inference(rectify,[],[f36])).
% 1.52/0.55  fof(f36,plain,(
% 1.52/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.55    inference(nnf_transformation,[],[f1])).
% 1.52/0.55  fof(f1,axiom,(
% 1.52/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.52/0.55  fof(f62,plain,(
% 1.52/0.55    ( ! [X4] : (r2_hidden(k3_funct_2(sK4,sK5,sK6,X4),sK3) | ~m1_subset_1(X4,sK4)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f35])).
% 1.52/0.55  fof(f564,plain,(
% 1.52/0.55    ~spl12_1),
% 1.52/0.55    inference(avatar_contradiction_clause,[],[f563])).
% 1.52/0.55  fof(f563,plain,(
% 1.52/0.55    $false | ~spl12_1),
% 1.52/0.55    inference(subsumption_resolution,[],[f561,f57])).
% 1.52/0.55  fof(f57,plain,(
% 1.52/0.55    ~v1_xboole_0(sK4)),
% 1.52/0.55    inference(cnf_transformation,[],[f35])).
% 1.52/0.55  fof(f561,plain,(
% 1.52/0.55    v1_xboole_0(sK4) | ~spl12_1),
% 1.52/0.55    inference(resolution,[],[f559,f66])).
% 1.52/0.55  fof(f66,plain,(
% 1.52/0.55    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f39])).
% 1.52/0.55  fof(f559,plain,(
% 1.52/0.55    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | ~spl12_1),
% 1.52/0.55    inference(resolution,[],[f106,f67])).
% 1.52/0.55  fof(f67,plain,(
% 1.52/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f16])).
% 1.52/0.55  fof(f16,plain,(
% 1.52/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.52/0.55    inference(ennf_transformation,[],[f4])).
% 1.52/0.55  fof(f4,axiom,(
% 1.52/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.52/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.52/0.55  fof(f106,plain,(
% 1.52/0.55    ( ! [X0] : (~m1_subset_1(X0,sK4)) ) | ~spl12_1),
% 1.52/0.55    inference(avatar_component_clause,[],[f105])).
% 1.52/0.55  fof(f464,plain,(
% 1.52/0.55    spl12_5 | spl12_6),
% 1.52/0.55    inference(avatar_split_clause,[],[f463,f320,f316])).
% 1.52/0.55  fof(f316,plain,(
% 1.52/0.55    spl12_5 <=> r2_hidden(sK6,k1_funct_2(sK4,sK5))),
% 1.52/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 1.52/0.55  fof(f320,plain,(
% 1.52/0.55    spl12_6 <=> k1_xboole_0 = sK5),
% 1.52/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.52/0.55  fof(f463,plain,(
% 1.52/0.55    r2_hidden(sK6,k1_funct_2(sK4,sK5)) | spl12_6),
% 1.52/0.55    inference(subsumption_resolution,[],[f462,f59])).
% 1.52/0.55  fof(f59,plain,(
% 1.52/0.55    v1_funct_1(sK6)),
% 1.52/0.55    inference(cnf_transformation,[],[f35])).
% 1.52/0.55  fof(f462,plain,(
% 1.52/0.55    r2_hidden(sK6,k1_funct_2(sK4,sK5)) | ~v1_funct_1(sK6) | spl12_6),
% 1.52/0.55    inference(subsumption_resolution,[],[f461,f60])).
% 1.52/0.55  fof(f60,plain,(
% 1.52/0.55    v1_funct_2(sK6,sK4,sK5)),
% 1.52/0.55    inference(cnf_transformation,[],[f35])).
% 1.52/0.55  fof(f461,plain,(
% 1.52/0.55    r2_hidden(sK6,k1_funct_2(sK4,sK5)) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | spl12_6),
% 1.52/0.55    inference(subsumption_resolution,[],[f456,f321])).
% 1.52/0.55  fof(f321,plain,(
% 1.52/0.55    k1_xboole_0 != sK5 | spl12_6),
% 1.52/0.55    inference(avatar_component_clause,[],[f320])).
% 1.52/0.55  fof(f456,plain,(
% 1.52/0.55    k1_xboole_0 = sK5 | r2_hidden(sK6,k1_funct_2(sK4,sK5)) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)),
% 1.52/0.55    inference(resolution,[],[f61,f78])).
% 1.52/0.55  fof(f434,plain,(
% 1.52/0.55    spl12_12 | ~spl12_5 | spl12_11),
% 1.52/0.55    inference(avatar_split_clause,[],[f414,f405,f316,f409])).
% 1.52/0.55  fof(f405,plain,(
% 1.52/0.55    spl12_11 <=> m1_subset_1(sK8(sK4,sK3,sK6),sK4)),
% 1.52/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 1.52/0.55  fof(f414,plain,(
% 1.52/0.55    sP0(sK3,sK4,sK6) | (~spl12_5 | spl12_11)),
% 1.52/0.55    inference(resolution,[],[f413,f351])).
% 1.52/0.55  fof(f351,plain,(
% 1.52/0.55    ( ! [X1] : (r2_hidden(sK8(sK4,X1,sK6),sK4) | sP0(X1,sK4,sK6)) ) | ~spl12_5),
% 1.52/0.55    inference(subsumption_resolution,[],[f350,f113])).
% 1.52/0.55  fof(f113,plain,(
% 1.52/0.55    v1_relat_1(sK6)),
% 1.52/0.55    inference(resolution,[],[f71,f61])).
% 1.52/0.55  fof(f71,plain,(
% 1.52/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f17])).
% 1.52/0.55  fof(f17,plain,(
% 1.52/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.55    inference(ennf_transformation,[],[f5])).
% 1.52/0.55  fof(f5,axiom,(
% 1.52/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.52/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.52/0.55  fof(f350,plain,(
% 1.52/0.55    ( ! [X1] : (r2_hidden(sK8(sK4,X1,sK6),sK4) | sP0(X1,sK4,sK6) | ~v1_relat_1(sK6)) ) | ~spl12_5),
% 1.52/0.55    inference(subsumption_resolution,[],[f345,f59])).
% 1.52/0.55  fof(f345,plain,(
% 1.52/0.55    ( ! [X1] : (r2_hidden(sK8(sK4,X1,sK6),sK4) | sP0(X1,sK4,sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl12_5),
% 1.52/0.55    inference(superposition,[],[f98,f330])).
% 1.52/0.55  fof(f330,plain,(
% 1.52/0.55    sK4 = k1_relat_1(sK6) | ~spl12_5),
% 1.52/0.55    inference(resolution,[],[f326,f132])).
% 1.52/0.55  fof(f132,plain,(
% 1.52/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | k1_relat_1(X2) = X1) )),
% 1.52/0.55    inference(duplicate_literal_removal,[],[f131])).
% 1.52/0.55  fof(f131,plain,(
% 1.52/0.55    ( ! [X2,X0,X1] : (k1_relat_1(X2) = X1 | ~sP1(X0,X1,X2) | ~sP1(X0,X1,X2)) )),
% 1.52/0.55    inference(superposition,[],[f89,f88])).
% 1.52/0.55  fof(f89,plain,(
% 1.52/0.55    ( ! [X2,X0,X1] : (k1_relat_1(sK11(X0,X1,X2)) = X1 | ~sP1(X0,X1,X2)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f55])).
% 1.52/0.55  fof(f326,plain,(
% 1.52/0.55    sP1(sK5,sK4,sK6) | ~spl12_5),
% 1.52/0.55    inference(resolution,[],[f318,f124])).
% 1.52/0.55  fof(f318,plain,(
% 1.52/0.55    r2_hidden(sK6,k1_funct_2(sK4,sK5)) | ~spl12_5),
% 1.52/0.55    inference(avatar_component_clause,[],[f316])).
% 1.52/0.55  fof(f98,plain,(
% 1.52/0.55    ( ! [X2,X1] : (r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP0(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.52/0.55    inference(equality_resolution,[],[f76])).
% 1.52/0.55  fof(f76,plain,(
% 1.52/0.55    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | r2_hidden(sK8(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f45])).
% 1.52/0.55  fof(f45,plain,(
% 1.52/0.55    ! [X0,X1,X2] : (sP0(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.52/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f28,f44])).
% 1.52/0.55  fof(f44,plain,(
% 1.52/0.55    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 1.52/0.55    introduced(choice_axiom,[])).
% 1.52/0.55  fof(f28,plain,(
% 1.52/0.55    ! [X0,X1,X2] : (sP0(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.52/0.55    inference(definition_folding,[],[f20,f27])).
% 1.52/0.55  fof(f20,plain,(
% 1.52/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.52/0.55    inference(flattening,[],[f19])).
% 1.52/0.55  fof(f19,plain,(
% 1.52/0.55    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.52/0.55    inference(ennf_transformation,[],[f11])).
% 1.52/0.55  fof(f11,axiom,(
% 1.52/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.52/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 1.52/0.55  fof(f413,plain,(
% 1.52/0.55    ~r2_hidden(sK8(sK4,sK3,sK6),sK4) | spl12_11),
% 1.52/0.55    inference(resolution,[],[f407,f67])).
% 1.52/0.55  fof(f407,plain,(
% 1.52/0.55    ~m1_subset_1(sK8(sK4,sK3,sK6),sK4) | spl12_11),
% 1.52/0.55    inference(avatar_component_clause,[],[f405])).
% 1.52/0.55  fof(f433,plain,(
% 1.52/0.55    ~spl12_6),
% 1.52/0.55    inference(avatar_contradiction_clause,[],[f432])).
% 1.52/0.55  fof(f432,plain,(
% 1.52/0.55    $false | ~spl12_6),
% 1.52/0.55    inference(subsumption_resolution,[],[f425,f64])).
% 1.52/0.55  fof(f425,plain,(
% 1.52/0.55    ~v1_xboole_0(k1_xboole_0) | ~spl12_6),
% 1.52/0.55    inference(backward_demodulation,[],[f58,f322])).
% 1.52/0.55  fof(f322,plain,(
% 1.52/0.55    k1_xboole_0 = sK5 | ~spl12_6),
% 1.52/0.55    inference(avatar_component_clause,[],[f320])).
% 1.52/0.55  fof(f58,plain,(
% 1.52/0.55    ~v1_xboole_0(sK5)),
% 1.52/0.55    inference(cnf_transformation,[],[f35])).
% 1.52/0.55  fof(f412,plain,(
% 1.52/0.55    ~spl12_11 | spl12_12 | ~spl12_5),
% 1.52/0.55    inference(avatar_split_clause,[],[f403,f316,f409,f405])).
% 1.52/0.55  fof(f403,plain,(
% 1.52/0.55    sP0(sK3,sK4,sK6) | ~m1_subset_1(sK8(sK4,sK3,sK6),sK4) | ~spl12_5),
% 1.52/0.55    inference(forward_demodulation,[],[f402,f330])).
% 1.52/0.55  fof(f402,plain,(
% 1.52/0.55    ~m1_subset_1(sK8(sK4,sK3,sK6),sK4) | sP0(sK3,k1_relat_1(sK6),sK6) | ~spl12_5),
% 1.52/0.55    inference(forward_demodulation,[],[f401,f330])).
% 1.52/0.55  fof(f401,plain,(
% 1.52/0.55    ~m1_subset_1(sK8(k1_relat_1(sK6),sK3,sK6),sK4) | sP0(sK3,k1_relat_1(sK6),sK6)),
% 1.52/0.55    inference(subsumption_resolution,[],[f400,f113])).
% 1.52/0.55  fof(f400,plain,(
% 1.52/0.55    ~m1_subset_1(sK8(k1_relat_1(sK6),sK3,sK6),sK4) | sP0(sK3,k1_relat_1(sK6),sK6) | ~v1_relat_1(sK6)),
% 1.52/0.55    inference(subsumption_resolution,[],[f398,f59])).
% 1.52/0.55  fof(f398,plain,(
% 1.52/0.55    ~m1_subset_1(sK8(k1_relat_1(sK6),sK3,sK6),sK4) | sP0(sK3,k1_relat_1(sK6),sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 1.52/0.55    inference(resolution,[],[f397,f97])).
% 1.52/0.55  fof(f97,plain,(
% 1.52/0.55    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1) | sP0(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.52/0.55    inference(equality_resolution,[],[f77])).
% 1.52/0.55  fof(f77,plain,(
% 1.52/0.55    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f45])).
% 1.52/0.55  fof(f397,plain,(
% 1.52/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK6,X0),sK3) | ~m1_subset_1(X0,sK4)) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f396,f57])).
% 1.52/0.55  fof(f396,plain,(
% 1.52/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK6,X0),sK3) | ~m1_subset_1(X0,sK4) | v1_xboole_0(sK4)) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f395,f59])).
% 1.52/0.55  fof(f395,plain,(
% 1.52/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK6,X0),sK3) | ~m1_subset_1(X0,sK4) | ~v1_funct_1(sK6) | v1_xboole_0(sK4)) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f394,f60])).
% 1.52/0.55  fof(f394,plain,(
% 1.52/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK6,X0),sK3) | ~m1_subset_1(X0,sK4) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK4)) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f393,f61])).
% 1.52/0.55  fof(f393,plain,(
% 1.52/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK6,X0),sK3) | ~m1_subset_1(X0,sK4) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK4)) )),
% 1.52/0.55    inference(duplicate_literal_removal,[],[f392])).
% 1.52/0.55  fof(f392,plain,(
% 1.52/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK6,X0),sK3) | ~m1_subset_1(X0,sK4) | ~m1_subset_1(X0,sK4) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK4)) )),
% 1.52/0.55    inference(superposition,[],[f62,f94])).
% 1.52/0.55  fof(f94,plain,(
% 1.52/0.55    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f26])).
% 1.52/0.55  fof(f26,plain,(
% 1.52/0.55    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.52/0.55    inference(flattening,[],[f25])).
% 1.52/0.55  fof(f25,plain,(
% 1.52/0.55    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.52/0.55    inference(ennf_transformation,[],[f8])).
% 1.52/0.55  fof(f8,axiom,(
% 1.52/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.52/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.52/0.55  % SZS output end Proof for theBenchmark
% 1.52/0.55  % (27796)------------------------------
% 1.52/0.55  % (27796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (27796)Termination reason: Refutation
% 1.52/0.55  
% 1.52/0.55  % (27796)Memory used [KB]: 6396
% 1.52/0.55  % (27796)Time elapsed: 0.135 s
% 1.52/0.55  % (27796)------------------------------
% 1.52/0.55  % (27796)------------------------------
% 1.52/0.55  % (27791)Success in time 0.193 s
%------------------------------------------------------------------------------
