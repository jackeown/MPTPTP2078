%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1051+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 208 expanded)
%              Number of leaves         :   23 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  352 ( 941 expanded)
%              Number of equality atoms :   41 ( 191 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f69,f93,f132,f152,f170,f176,f189,f192,f193])).

fof(f193,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f192,plain,
    ( ~ spl6_5
    | ~ spl6_13
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_13
    | spl6_16 ),
    inference(subsumption_resolution,[],[f190,f187])).

fof(f187,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_16
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f190,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f63,f162,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,X3)
      | ~ r1_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_relset_1(X0,X1,X2,X3)
          | ~ r1_tarski(X2,X3) )
        & ( r1_tarski(X2,X3)
          | ~ r1_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_relset_1)).

fof(f162,plain,
    ( r1_relset_1(sK0,sK1,sK2,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_13
  <=> r1_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f189,plain,
    ( spl6_15
    | ~ spl6_16
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f179,f173,f185,f181])).

fof(f181,plain,
    ( spl6_15
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f173,plain,
    ( spl6_14
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f179,plain,
    ( ~ r1_tarski(sK2,sK3)
    | sK2 = sK3
    | ~ spl6_14 ),
    inference(resolution,[],[f175,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f175,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f173])).

fof(f176,plain,
    ( spl6_14
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f171,f142,f51,f173])).

fof(f51,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f142,plain,
    ( spl6_12
  <=> r1_relset_1(sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f171,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f53,f144,f34])).

fof(f144,plain,
    ( r1_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f53,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f170,plain,
    ( spl6_13
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f169,f66,f61,f56,f51,f46,f160])).

fof(f46,plain,
    ( spl6_2
  <=> k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f56,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f66,plain,
    ( spl6_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f169,plain,
    ( r1_relset_1(sK0,sK1,sK2,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f168,f68])).

fof(f68,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f168,plain,
    ( r1_relset_1(sK0,sK1,sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f156,f63])).

fof(f156,plain,
    ( r1_relset_1(sK0,sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f119,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f119,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1))
        | r1_relset_1(sK0,sK1,X1,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f118,f58])).

fof(f58,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1))
        | r1_relset_1(sK0,sK1,X1,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f117,f53])).

fof(f117,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1))
        | r1_relset_1(sK0,sK1,X1,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f26,plain,(
    ! [X4] : k1_tarski(X4) != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)
    & ! [X4] : k1_tarski(X4) != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
            & ! [X4] : k1_tarski(X4) != X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,X3)
          & ! [X4] : k1_tarski(X4) != sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,X3)
        & ! [X4] : k1_tarski(X4) != sK1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)
      & ! [X4] : k1_tarski(X4) != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
                & ! [X4] : k1_tarski(X4) != X1 )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
              & ! [X4] : k1_tarski(X4) != X1 )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_2)).

fof(f113,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1))
        | sK1 = k1_tarski(sK4(sK1))
        | r1_relset_1(sK0,sK1,X1,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl6_2 ),
    inference(superposition,[],[f30,f48])).

fof(f48,plain,
    ( k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
      | k1_tarski(sK4(X1)) = X1
      | r1_relset_1(X0,X1,X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | k1_tarski(sK4(X1)) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f17])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X4] : k1_tarski(X4) = X1
     => k1_tarski(sK4(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( ! [X4] : k1_tarski(X4) != X1
              & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) )
           => r1_relset_1(X0,X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_2)).

fof(f152,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f151,f66,f61,f56,f51,f46,f142])).

fof(f151,plain,
    ( r1_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f150,f68])).

fof(f150,plain,
    ( r1_relset_1(sK0,sK1,sK3,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f138,f63])).

fof(f138,plain,
    ( r1_relset_1(sK0,sK1,sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f116,f36])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
        | r1_relset_1(sK0,sK1,sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f115,f58])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
        | r1_relset_1(sK0,sK1,sK3,X0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f114,f53])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
        | r1_relset_1(sK0,sK1,sK3,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f112,f26])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
        | sK1 = k1_tarski(sK4(sK1))
        | r1_relset_1(sK0,sK1,sK3,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f30,f48])).

fof(f132,plain,
    ( spl6_11
    | ~ spl6_3
    | spl6_7 ),
    inference(avatar_split_clause,[],[f120,f79,f51,f129])).

fof(f129,plain,
    ( spl6_11
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f79,plain,
    ( spl6_7
  <=> sP5(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f120,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl6_3
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f53,f81,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f38_D])).

fof(f38_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP5(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f81,plain,
    ( ~ sP5(sK1,sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,
    ( ~ spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f77,f51,f79])).

fof(f77,plain,
    ( ~ sP5(sK1,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f53,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP5(X1,X0) ) ),
    inference(general_splitting,[],[f29,f38_D])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f69,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f22,f66])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f27,f46])).

fof(f27,plain,(
    k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f28,f41])).

fof(f41,plain,
    ( spl6_1
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f28,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
