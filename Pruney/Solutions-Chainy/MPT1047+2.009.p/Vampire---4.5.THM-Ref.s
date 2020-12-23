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
% DateTime   : Thu Dec  3 13:07:01 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 822 expanded)
%              Number of leaves         :   28 ( 269 expanded)
%              Depth                    :   22
%              Number of atoms          :  670 (3280 expanded)
%              Number of equality atoms :  157 ( 778 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f246,f291,f383,f458,f1010,f2122])).

fof(f2122,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f2121])).

fof(f2121,plain,
    ( $false
    | spl10_3 ),
    inference(subsumption_resolution,[],[f2120,f107])).

fof(f107,plain,(
    k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f63,f106,f106])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f105])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK3,k1_tarski(sK4),sK5)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
          & v1_funct_2(X3,sK3,k1_tarski(sK4))
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK3,k1_tarski(sK4),sK5)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
        & v1_funct_2(X3,sK3,k1_tarski(sK4))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_2(sK6,sK3,k1_tarski(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(f2120,plain,
    ( k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK6,sK6,sK6,sK6)
    | spl10_3 ),
    inference(equality_resolution,[],[f1868])).

fof(f1868,plain,
    ( ! [X15] :
        ( sK6 != X15
        | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X15,X15,X15,X15) )
    | spl10_3 ),
    inference(subsumption_resolution,[],[f1769,f212])).

fof(f212,plain,
    ( k1_xboole_0 != k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl10_3
  <=> k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1769,plain,
    ( ! [X15] :
        ( sK6 != X15
        | k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)
        | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X15,X15,X15,X15) )
    | spl10_3 ),
    inference(duplicate_literal_removal,[],[f1768])).

fof(f1768,plain,
    ( ! [X15] :
        ( sK6 != X15
        | k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)
        | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X15,X15,X15,X15)
        | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X15,X15,X15,X15) )
    | spl10_3 ),
    inference(superposition,[],[f111,f1646])).

fof(f1646,plain,
    ( ! [X21] :
        ( k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X21,X21,X21,X21)
        | sK6 = sK7(k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5),X21) )
    | spl10_3 ),
    inference(subsumption_resolution,[],[f1645,f212])).

fof(f1645,plain,(
    ! [X21] :
      ( k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)
      | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X21,X21,X21,X21)
      | sK6 = sK7(k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5),X21) ) ),
    inference(subsumption_resolution,[],[f1609,f166])).

fof(f166,plain,(
    sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(subsumption_resolution,[],[f164,f58])).

fof(f58,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f164,plain,
    ( sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f89,f110])).

fof(f110,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f59,f106])).

fof(f59,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f28,f36,f35,f34])).

fof(f34,plain,(
    ! [X2,X0,X4,X1] :
      ( sP0(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X1,X0,X2,X3] :
      ( sP1(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP1(X1,X0,X2,X3) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f1609,plain,(
    ! [X21] :
      ( ~ sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
      | k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)
      | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X21,X21,X21,X21)
      | sK6 = sK7(k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5),X21) ) ),
    inference(resolution,[],[f183,f611])).

fof(f611,plain,(
    ! [X0] :
      ( ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))
      | sK6 = X0 ) ),
    inference(global_subsumption,[],[f209,f441,f498,f563,f606])).

fof(f606,plain,(
    ! [X0] :
      ( sK6 = X0
      | ~ r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X0,sK6)
      | ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) ) ),
    inference(resolution,[],[f299,f563])).

fof(f299,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | sK6 = X0
      | ~ r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X0,sK6) ) ),
    inference(resolution,[],[f94,f108])).

fof(f108,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f62,f106])).

fof(f62,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f563,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) ) ),
    inference(subsumption_resolution,[],[f560,f166])).

fof(f560,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ) ),
    inference(resolution,[],[f279,f168])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k5_partfun1(X1,X3,X0))
      | ~ sP0(X0,X1,X2,X3)
      | ~ sP2(X0,X1,X3) ) ),
    inference(resolution,[],[f80,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP1(X2,X1,X0,X3) )
          & ( sP1(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP1(X1,X0,X2,X3) )
          & ( sP1(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X2,X1,X5,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f47])).

fof(f47,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X2,X1,X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X2,X1,X4,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X1,X4,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X2,X1,X4,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP1(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X2,X0,X4,X1)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X2,X0,X4,X1) )
            & ( sP0(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f279,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5))
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) ) ),
    inference(subsumption_resolution,[],[f276,f58])).

fof(f276,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5))
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f76,f110])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f498,plain,(
    ! [X0] :
      ( ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))
      | v1_funct_2(X0,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ) ),
    inference(subsumption_resolution,[],[f495,f166])).

fof(f495,plain,(
    ! [X0] :
      ( v1_funct_2(X0,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ) ),
    inference(resolution,[],[f222,f168])).

fof(f222,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5))
      | v1_funct_2(X1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ) ),
    inference(subsumption_resolution,[],[f219,f58])).

fof(f219,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5))
      | v1_funct_2(X1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f75,f110])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f441,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X5,sK6)
      | ~ v1_funct_2(X5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f440,f60])).

fof(f60,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f440,plain,(
    ! [X5] :
      ( r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X5,sK6)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | ~ v1_funct_2(X5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f437,f109])).

fof(f109,plain,(
    v1_funct_2(sK6,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f61,f106])).

fof(f61,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f437,plain,(
    ! [X5] :
      ( r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X5,sK6)
      | ~ v1_funct_2(sK6,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | ~ v1_funct_2(X5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f113,f108])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3)
      | ~ v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f71,f106,f106,f106,f106,f106])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_2)).

fof(f209,plain,(
    ! [X0] :
      ( ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))
      | v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f207,f166])).

fof(f207,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ) ),
    inference(resolution,[],[f194,f168])).

fof(f194,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5))
      | v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f191,f58])).

fof(f191,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5))
      | v1_funct_1(X1)
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f74,f110])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,sK7(k5_partfun1(X1,X2,X0),X3),X2)
      | ~ sP2(X0,X1,X2)
      | k1_xboole_0 = k5_partfun1(X1,X2,X0)
      | k5_partfun1(X1,X2,X0) = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(resolution,[],[f167,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f68,f106])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sK7(X0,X1) != X1
        & r2_hidden(sK7(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK7(X0,X1) != X1
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
      | sP0(X3,X1,X0,X2)
      | ~ sP2(X3,X1,X2) ) ),
    inference(resolution,[],[f79,f128])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP0(X2,X1,X5,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sK7(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f69,f106])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sK7(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1010,plain,(
    ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f1009])).

fof(f1009,plain,
    ( $false
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f1008,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1008,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6)
    | ~ spl10_11 ),
    inference(resolution,[],[f290,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f290,plain,
    ( r2_hidden(sK6,k1_xboole_0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl10_11
  <=> r2_hidden(sK6,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f458,plain,(
    spl10_10 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | spl10_10 ),
    inference(subsumption_resolution,[],[f456,f58])).

fof(f456,plain,
    ( ~ v1_funct_1(sK5)
    | spl10_10 ),
    inference(subsumption_resolution,[],[f453,f286])).

fof(f286,plain,
    ( ~ r1_partfun1(sK5,sK6)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl10_10
  <=> r1_partfun1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f453,plain,
    ( r1_partfun1(sK5,sK6)
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f427,f110])).

fof(f427,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | r1_partfun1(X5,sK6)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f424,f60])).

% (16785)Refutation not found, incomplete strategy% (16785)------------------------------
% (16785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f424,plain,(
    ! [X5] :
      ( r1_partfun1(X5,sK6)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f114,f108])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f90,f106,f106])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(f383,plain,(
    ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f370,f64])).

fof(f370,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | ~ spl10_6 ),
    inference(superposition,[],[f152,f245])).

fof(f245,plain,
    ( k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl10_6
  <=> k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f152,plain,(
    ! [X2,X0,X1] : ~ r1_tarski(k2_enumset1(X0,X0,X1,X2),X1) ),
    inference(resolution,[],[f149,f67])).

fof(f149,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(resolution,[],[f133,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f91,f105])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f133,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X1,X1,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f102,f70,f105])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k2_tarski(X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f291,plain,
    ( ~ spl10_10
    | spl10_11
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f282,f239,f211,f288,f284])).

fof(f239,plain,
    ( spl10_5
  <=> v1_partfun1(sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f282,plain,
    ( r2_hidden(sK6,k1_xboole_0)
    | ~ r1_partfun1(sK5,sK6)
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(resolution,[],[f229,f264])).

fof(f264,plain,
    ( ! [X0] :
        ( sP0(X0,sK3,sK6,k2_enumset1(sK4,sK4,sK4,sK4))
        | ~ r1_partfun1(X0,sK6) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f263,f60])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK6)
        | sP0(X0,sK3,sK6,k2_enumset1(sK4,sK4,sK4,sK4))
        | ~ v1_funct_1(sK6) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f260,f241])).

fof(f241,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f239])).

fof(f260,plain,(
    ! [X0] :
      ( ~ r1_partfun1(X0,sK6)
      | ~ v1_partfun1(sK6,sK3)
      | sP0(X0,sK3,sK6,k2_enumset1(sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f129,f108])).

fof(f129,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | sP0(X0,X1,X4,X3)
      | ~ v1_funct_1(X4) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ( r1_partfun1(X0,sK9(X0,X1,X2,X3))
          & v1_partfun1(sK9(X0,X1,X2,X3),X1)
          & sK9(X0,X1,X2,X3) = X2
          & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(sK9(X0,X1,X2,X3)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_partfun1(X0,X5)
          & v1_partfun1(X5,X1)
          & X2 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(X5) )
     => ( r1_partfun1(X0,sK9(X0,X1,X2,X3))
        & v1_partfun1(sK9(X0,X1,X2,X3),X1)
        & sK9(X0,X1,X2,X3) = X2
        & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & v1_funct_1(sK9(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ? [X5] :
            ( r1_partfun1(X0,X5)
            & v1_partfun1(X5,X1)
            & X2 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            & v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X4,X1] :
      ( ( sP0(X2,X0,X4,X1)
        | ! [X5] :
            ( ~ r1_partfun1(X2,X5)
            | ~ v1_partfun1(X5,X0)
            | X4 != X5
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_1(X5) ) )
      & ( ? [X5] :
            ( r1_partfun1(X2,X5)
            & v1_partfun1(X5,X0)
            & X4 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X5) )
        | ~ sP0(X2,X0,X4,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f226,f166])).

fof(f226,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))
        | ~ sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) )
    | ~ spl10_3 ),
    inference(superposition,[],[f168,f213])).

fof(f213,plain,
    ( k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f211])).

fof(f246,plain,
    ( spl10_5
    | spl10_6 ),
    inference(avatar_split_clause,[],[f237,f243,f239])).

fof(f237,plain,
    ( k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4)
    | v1_partfun1(sK6,sK3) ),
    inference(subsumption_resolution,[],[f236,f60])).

fof(f236,plain,
    ( k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4)
    | v1_partfun1(sK6,sK3)
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f233,f109])).

fof(f233,plain,
    ( k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4)
    | v1_partfun1(sK6,sK3)
    | ~ v1_funct_2(sK6,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ v1_funct_1(sK6) ),
    inference(resolution,[],[f140,f108])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:13:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (16787)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (16803)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (16800)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (16808)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (16791)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (16793)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (16799)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (16788)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (16792)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (16790)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (16785)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (16801)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (16786)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (16786)Refutation not found, incomplete strategy% (16786)------------------------------
% 0.21/0.53  % (16786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16786)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16786)Memory used [KB]: 1663
% 0.21/0.53  % (16786)Time elapsed: 0.128 s
% 0.21/0.53  % (16786)------------------------------
% 0.21/0.53  % (16786)------------------------------
% 0.21/0.53  % (16812)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (16795)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (16789)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (16814)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (16804)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (16814)Refutation not found, incomplete strategy% (16814)------------------------------
% 0.21/0.54  % (16814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16814)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16814)Memory used [KB]: 1663
% 0.21/0.54  % (16814)Time elapsed: 0.001 s
% 0.21/0.54  % (16814)------------------------------
% 0.21/0.54  % (16814)------------------------------
% 0.21/0.54  % (16798)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (16809)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (16796)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (16802)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (16806)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (16809)Refutation not found, incomplete strategy% (16809)------------------------------
% 0.21/0.55  % (16809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16809)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16809)Memory used [KB]: 10746
% 0.21/0.55  % (16809)Time elapsed: 0.148 s
% 0.21/0.55  % (16809)------------------------------
% 0.21/0.55  % (16809)------------------------------
% 0.21/0.55  % (16813)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (16794)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (16805)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (16807)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (16811)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (16797)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % (16797)Refutation not found, incomplete strategy% (16797)------------------------------
% 0.21/0.57  % (16797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (16797)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (16797)Memory used [KB]: 10618
% 0.21/0.57  % (16797)Time elapsed: 0.169 s
% 0.21/0.57  % (16797)------------------------------
% 0.21/0.57  % (16797)------------------------------
% 0.21/0.57  % (16810)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.98/0.62  % (16791)Refutation found. Thanks to Tanya!
% 1.98/0.62  % SZS status Theorem for theBenchmark
% 1.98/0.62  % SZS output start Proof for theBenchmark
% 1.98/0.62  fof(f2123,plain,(
% 1.98/0.62    $false),
% 1.98/0.62    inference(avatar_sat_refutation,[],[f246,f291,f383,f458,f1010,f2122])).
% 1.98/0.62  fof(f2122,plain,(
% 1.98/0.62    spl10_3),
% 1.98/0.62    inference(avatar_contradiction_clause,[],[f2121])).
% 1.98/0.62  fof(f2121,plain,(
% 1.98/0.62    $false | spl10_3),
% 1.98/0.62    inference(subsumption_resolution,[],[f2120,f107])).
% 1.98/0.62  fof(f107,plain,(
% 1.98/0.62    k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK6,sK6,sK6,sK6)),
% 1.98/0.62    inference(definition_unfolding,[],[f63,f106,f106])).
% 1.98/0.62  fof(f106,plain,(
% 1.98/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.98/0.62    inference(definition_unfolding,[],[f65,f105])).
% 1.98/0.62  fof(f105,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.98/0.62    inference(definition_unfolding,[],[f66,f70])).
% 1.98/0.62  fof(f70,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f4])).
% 1.98/0.62  fof(f4,axiom,(
% 1.98/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.98/0.62  fof(f66,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f3])).
% 1.98/0.62  fof(f3,axiom,(
% 1.98/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.98/0.62  fof(f65,plain,(
% 1.98/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f2])).
% 1.98/0.62  fof(f2,axiom,(
% 1.98/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.98/0.62  fof(f63,plain,(
% 1.98/0.62    k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6)),
% 1.98/0.62    inference(cnf_transformation,[],[f40])).
% 1.98/0.62  fof(f40,plain,(
% 1.98/0.62    (k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_1(sK5)),
% 1.98/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f39,f38])).
% 1.98/0.62  fof(f38,plain,(
% 1.98/0.62    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK3,k1_tarski(sK4),sK5) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(X3,sK3,k1_tarski(sK4)) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_1(sK5))),
% 1.98/0.62    introduced(choice_axiom,[])).
% 1.98/0.62  fof(f39,plain,(
% 1.98/0.62    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK3,k1_tarski(sK4),sK5) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(X3,sK3,k1_tarski(sK4)) & v1_funct_1(X3)) => (k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 1.98/0.62    introduced(choice_axiom,[])).
% 1.98/0.62  fof(f18,plain,(
% 1.98/0.62    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 1.98/0.62    inference(flattening,[],[f17])).
% 1.98/0.62  fof(f17,plain,(
% 1.98/0.62    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 1.98/0.62    inference(ennf_transformation,[],[f16])).
% 1.98/0.62  fof(f16,negated_conjecture,(
% 1.98/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 1.98/0.62    inference(negated_conjecture,[],[f15])).
% 1.98/0.62  fof(f15,conjecture,(
% 1.98/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).
% 1.98/0.62  fof(f2120,plain,(
% 1.98/0.62    k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK6,sK6,sK6,sK6) | spl10_3),
% 1.98/0.62    inference(equality_resolution,[],[f1868])).
% 1.98/0.62  fof(f1868,plain,(
% 1.98/0.62    ( ! [X15] : (sK6 != X15 | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X15,X15,X15,X15)) ) | spl10_3),
% 1.98/0.62    inference(subsumption_resolution,[],[f1769,f212])).
% 1.98/0.62  fof(f212,plain,(
% 1.98/0.62    k1_xboole_0 != k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) | spl10_3),
% 1.98/0.62    inference(avatar_component_clause,[],[f211])).
% 1.98/0.62  fof(f211,plain,(
% 1.98/0.62    spl10_3 <=> k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)),
% 1.98/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.98/0.62  fof(f1769,plain,(
% 1.98/0.62    ( ! [X15] : (sK6 != X15 | k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X15,X15,X15,X15)) ) | spl10_3),
% 1.98/0.62    inference(duplicate_literal_removal,[],[f1768])).
% 1.98/0.62  fof(f1768,plain,(
% 1.98/0.62    ( ! [X15] : (sK6 != X15 | k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X15,X15,X15,X15) | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X15,X15,X15,X15)) ) | spl10_3),
% 1.98/0.62    inference(superposition,[],[f111,f1646])).
% 1.98/0.62  fof(f1646,plain,(
% 1.98/0.62    ( ! [X21] : (k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X21,X21,X21,X21) | sK6 = sK7(k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5),X21)) ) | spl10_3),
% 1.98/0.62    inference(subsumption_resolution,[],[f1645,f212])).
% 1.98/0.62  fof(f1645,plain,(
% 1.98/0.62    ( ! [X21] : (k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X21,X21,X21,X21) | sK6 = sK7(k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5),X21)) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f1609,f166])).
% 1.98/0.62  fof(f166,plain,(
% 1.98/0.62    sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))),
% 1.98/0.62    inference(subsumption_resolution,[],[f164,f58])).
% 1.98/0.62  fof(f58,plain,(
% 1.98/0.62    v1_funct_1(sK5)),
% 1.98/0.62    inference(cnf_transformation,[],[f40])).
% 1.98/0.62  fof(f164,plain,(
% 1.98/0.62    sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK5)),
% 1.98/0.62    inference(resolution,[],[f89,f110])).
% 1.98/0.62  fof(f110,plain,(
% 1.98/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))),
% 1.98/0.62    inference(definition_unfolding,[],[f59,f106])).
% 1.98/0.62  fof(f59,plain,(
% 1.98/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 1.98/0.62    inference(cnf_transformation,[],[f40])).
% 1.98/0.62  fof(f89,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f37])).
% 1.98/0.62  fof(f37,plain,(
% 1.98/0.62    ! [X0,X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.98/0.62    inference(definition_folding,[],[f28,f36,f35,f34])).
% 1.98/0.62  fof(f34,plain,(
% 1.98/0.62    ! [X2,X0,X4,X1] : (sP0(X2,X0,X4,X1) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))),
% 1.98/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.98/0.62  fof(f35,plain,(
% 1.98/0.62    ! [X1,X0,X2,X3] : (sP1(X1,X0,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X2,X0,X4,X1)))),
% 1.98/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.98/0.62  fof(f36,plain,(
% 1.98/0.62    ! [X2,X0,X1] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP1(X1,X0,X2,X3)) | ~sP2(X2,X0,X1))),
% 1.98/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.98/0.62  fof(f28,plain,(
% 1.98/0.62    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.98/0.62    inference(flattening,[],[f27])).
% 1.98/0.62  fof(f27,plain,(
% 1.98/0.62    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.98/0.62    inference(ennf_transformation,[],[f10])).
% 1.98/0.62  fof(f10,axiom,(
% 1.98/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 1.98/0.62  fof(f1609,plain,(
% 1.98/0.62    ( ! [X21] : (~sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) | k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(X21,X21,X21,X21) | sK6 = sK7(k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5),X21)) )),
% 1.98/0.62    inference(resolution,[],[f183,f611])).
% 1.98/0.62  fof(f611,plain,(
% 1.98/0.62    ( ! [X0] : (~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) | sK6 = X0) )),
% 1.98/0.62    inference(global_subsumption,[],[f209,f441,f498,f563,f606])).
% 1.98/0.62  fof(f606,plain,(
% 1.98/0.62    ( ! [X0] : (sK6 = X0 | ~r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X0,sK6) | ~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))) )),
% 1.98/0.62    inference(resolution,[],[f299,f563])).
% 1.98/0.62  fof(f299,plain,(
% 1.98/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | sK6 = X0 | ~r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X0,sK6)) )),
% 1.98/0.62    inference(resolution,[],[f94,f108])).
% 1.98/0.62  fof(f108,plain,(
% 1.98/0.62    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))),
% 1.98/0.62    inference(definition_unfolding,[],[f62,f106])).
% 1.98/0.62  fof(f62,plain,(
% 1.98/0.62    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 1.98/0.62    inference(cnf_transformation,[],[f40])).
% 1.98/0.62  fof(f94,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.98/0.62    inference(cnf_transformation,[],[f55])).
% 1.98/0.62  fof(f55,plain,(
% 1.98/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/0.62    inference(nnf_transformation,[],[f32])).
% 1.98/0.62  fof(f32,plain,(
% 1.98/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/0.62    inference(flattening,[],[f31])).
% 1.98/0.62  fof(f31,plain,(
% 1.98/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.98/0.62    inference(ennf_transformation,[],[f9])).
% 1.98/0.62  fof(f9,axiom,(
% 1.98/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.98/0.62  fof(f563,plain,(
% 1.98/0.62    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | ~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4))) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f560,f166])).
% 1.98/0.62  fof(f560,plain,(
% 1.98/0.62    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | ~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) | ~sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))) )),
% 1.98/0.62    inference(resolution,[],[f279,f168])).
% 1.98/0.62  fof(f168,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(X2,k5_partfun1(X1,X3,X0)) | ~sP0(X0,X1,X2,X3) | ~sP2(X0,X1,X3)) )),
% 1.98/0.62    inference(resolution,[],[f80,f128])).
% 1.98/0.62  fof(f128,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k5_partfun1(X1,X2,X0)) | ~sP2(X0,X1,X2)) )),
% 1.98/0.62    inference(equality_resolution,[],[f77])).
% 1.98/0.62  fof(f77,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3 | ~sP2(X0,X1,X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f44])).
% 1.98/0.62  fof(f44,plain,(
% 1.98/0.62    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X2,X0) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3)) | ~sP2(X0,X1,X2))),
% 1.98/0.62    inference(rectify,[],[f43])).
% 1.98/0.62  fof(f43,plain,(
% 1.98/0.62    ! [X2,X0,X1] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP1(X1,X0,X2,X3)) & (sP1(X1,X0,X2,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP2(X2,X0,X1))),
% 1.98/0.62    inference(nnf_transformation,[],[f36])).
% 1.98/0.62  fof(f80,plain,(
% 1.98/0.62    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X2,X1,X5,X0) | r2_hidden(X5,X3)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f48])).
% 1.98/0.62  fof(f48,plain,(
% 1.98/0.62    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.98/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f47])).
% 1.98/0.62  fof(f47,plain,(
% 1.98/0.62    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3))) => ((~sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 1.98/0.62    introduced(choice_axiom,[])).
% 1.98/0.62  fof(f46,plain,(
% 1.98/0.62    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.98/0.62    inference(rectify,[],[f45])).
% 1.98/0.62  fof(f45,plain,(
% 1.98/0.62    ! [X1,X0,X2,X3] : ((sP1(X1,X0,X2,X3) | ? [X4] : ((~sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3)) & (sP0(X2,X0,X4,X1) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X2,X0,X4,X1)) & (sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3))) | ~sP1(X1,X0,X2,X3)))),
% 1.98/0.62    inference(nnf_transformation,[],[f35])).
% 1.98/0.62  fof(f279,plain,(
% 1.98/0.62    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4))))) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f276,f58])).
% 1.98/0.62  fof(f276,plain,(
% 1.98/0.62    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | ~v1_funct_1(sK5)) )),
% 1.98/0.62    inference(resolution,[],[f76,f110])).
% 1.98/0.62  fof(f76,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f26])).
% 1.98/0.62  fof(f26,plain,(
% 1.98/0.62    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.98/0.62    inference(flattening,[],[f25])).
% 1.98/0.62  fof(f25,plain,(
% 1.98/0.62    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.98/0.62    inference(ennf_transformation,[],[f13])).
% 1.98/0.62  fof(f13,axiom,(
% 1.98/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).
% 1.98/0.62  fof(f498,plain,(
% 1.98/0.62    ( ! [X0] : (~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) | v1_funct_2(X0,sK3,k2_enumset1(sK4,sK4,sK4,sK4))) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f495,f166])).
% 1.98/0.62  fof(f495,plain,(
% 1.98/0.62    ( ! [X0] : (v1_funct_2(X0,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | ~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) | ~sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))) )),
% 1.98/0.62    inference(resolution,[],[f222,f168])).
% 1.98/0.62  fof(f222,plain,(
% 1.98/0.62    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)) | v1_funct_2(X1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f219,f58])).
% 1.98/0.62  fof(f219,plain,(
% 1.98/0.62    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)) | v1_funct_2(X1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK5)) )),
% 1.98/0.62    inference(resolution,[],[f75,f110])).
% 1.98/0.62  fof(f75,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f26])).
% 1.98/0.62  fof(f441,plain,(
% 1.98/0.62    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X5,sK6) | ~v1_funct_2(X5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(X5)) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f440,f60])).
% 1.98/0.62  fof(f60,plain,(
% 1.98/0.62    v1_funct_1(sK6)),
% 1.98/0.62    inference(cnf_transformation,[],[f40])).
% 1.98/0.62  fof(f440,plain,(
% 1.98/0.62    ( ! [X5] : (r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X5,sK6) | ~v1_funct_1(sK6) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | ~v1_funct_2(X5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(X5)) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f437,f109])).
% 1.98/0.62  fof(f109,plain,(
% 1.98/0.62    v1_funct_2(sK6,sK3,k2_enumset1(sK4,sK4,sK4,sK4))),
% 1.98/0.62    inference(definition_unfolding,[],[f61,f106])).
% 1.98/0.62  fof(f61,plain,(
% 1.98/0.62    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 1.98/0.62    inference(cnf_transformation,[],[f40])).
% 1.98/0.62  fof(f437,plain,(
% 1.98/0.62    ( ! [X5] : (r2_relset_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),X5,sK6) | ~v1_funct_2(sK6,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK6) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | ~v1_funct_2(X5,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(X5)) )),
% 1.98/0.62    inference(resolution,[],[f113,f108])).
% 1.98/0.62  fof(f113,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3) | ~v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_funct_1(X2)) )),
% 1.98/0.62    inference(definition_unfolding,[],[f71,f106,f106,f106,f106,f106])).
% 1.98/0.62  fof(f71,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f22])).
% 1.98/0.62  fof(f22,plain,(
% 1.98/0.62    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2))),
% 1.98/0.62    inference(flattening,[],[f21])).
% 1.98/0.62  fof(f21,plain,(
% 1.98/0.62    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2)))),
% 1.98/0.62    inference(ennf_transformation,[],[f14])).
% 1.98/0.62  fof(f14,axiom,(
% 1.98/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_2)).
% 1.98/0.62  fof(f209,plain,(
% 1.98/0.62    ( ! [X0] : (~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) | v1_funct_1(X0)) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f207,f166])).
% 1.98/0.62  fof(f207,plain,(
% 1.98/0.62    ( ! [X0] : (v1_funct_1(X0) | ~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) | ~sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))) )),
% 1.98/0.62    inference(resolution,[],[f194,f168])).
% 1.98/0.62  fof(f194,plain,(
% 1.98/0.62    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)) | v1_funct_1(X1)) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f191,f58])).
% 1.98/0.62  fof(f191,plain,(
% 1.98/0.62    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5)) | v1_funct_1(X1) | ~v1_funct_1(sK5)) )),
% 1.98/0.62    inference(resolution,[],[f74,f110])).
% 1.98/0.62  fof(f74,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3) | ~v1_funct_1(X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f26])).
% 1.98/0.62  fof(f183,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,sK7(k5_partfun1(X1,X2,X0),X3),X2) | ~sP2(X0,X1,X2) | k1_xboole_0 = k5_partfun1(X1,X2,X0) | k5_partfun1(X1,X2,X0) = k2_enumset1(X3,X3,X3,X3)) )),
% 1.98/0.62    inference(resolution,[],[f167,f112])).
% 1.98/0.62  fof(f112,plain,(
% 1.98/0.62    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.98/0.62    inference(definition_unfolding,[],[f68,f106])).
% 1.98/0.62  fof(f68,plain,(
% 1.98/0.62    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.98/0.62    inference(cnf_transformation,[],[f42])).
% 1.98/0.62  fof(f42,plain,(
% 1.98/0.62    ! [X0,X1] : ((sK7(X0,X1) != X1 & r2_hidden(sK7(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.98/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f41])).
% 1.98/0.62  fof(f41,plain,(
% 1.98/0.62    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK7(X0,X1) != X1 & r2_hidden(sK7(X0,X1),X0)))),
% 1.98/0.62    introduced(choice_axiom,[])).
% 1.98/0.62  fof(f20,plain,(
% 1.98/0.62    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.98/0.62    inference(ennf_transformation,[],[f5])).
% 1.98/0.62  fof(f5,axiom,(
% 1.98/0.62    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.98/0.62  fof(f167,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k5_partfun1(X1,X2,X3)) | sP0(X3,X1,X0,X2) | ~sP2(X3,X1,X2)) )),
% 1.98/0.62    inference(resolution,[],[f79,f128])).
% 1.98/0.62  fof(f79,plain,(
% 1.98/0.62    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP0(X2,X1,X5,X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f48])).
% 1.98/0.62  fof(f111,plain,(
% 1.98/0.62    ( ! [X0,X1] : (sK7(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.98/0.62    inference(definition_unfolding,[],[f69,f106])).
% 1.98/0.62  fof(f69,plain,(
% 1.98/0.62    ( ! [X0,X1] : (sK7(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.98/0.62    inference(cnf_transformation,[],[f42])).
% 1.98/0.62  fof(f1010,plain,(
% 1.98/0.62    ~spl10_11),
% 1.98/0.62    inference(avatar_contradiction_clause,[],[f1009])).
% 1.98/0.62  fof(f1009,plain,(
% 1.98/0.62    $false | ~spl10_11),
% 1.98/0.62    inference(subsumption_resolution,[],[f1008,f64])).
% 1.98/0.62  fof(f64,plain,(
% 1.98/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f1])).
% 1.98/0.62  fof(f1,axiom,(
% 1.98/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.98/0.62  fof(f1008,plain,(
% 1.98/0.62    ~r1_tarski(k1_xboole_0,sK6) | ~spl10_11),
% 1.98/0.62    inference(resolution,[],[f290,f67])).
% 1.98/0.62  fof(f67,plain,(
% 1.98/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f19])).
% 1.98/0.62  fof(f19,plain,(
% 1.98/0.62    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.98/0.62    inference(ennf_transformation,[],[f8])).
% 1.98/0.62  fof(f8,axiom,(
% 1.98/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.98/0.62  fof(f290,plain,(
% 1.98/0.62    r2_hidden(sK6,k1_xboole_0) | ~spl10_11),
% 1.98/0.62    inference(avatar_component_clause,[],[f288])).
% 1.98/0.62  fof(f288,plain,(
% 1.98/0.62    spl10_11 <=> r2_hidden(sK6,k1_xboole_0)),
% 1.98/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.98/0.62  fof(f458,plain,(
% 1.98/0.62    spl10_10),
% 1.98/0.62    inference(avatar_contradiction_clause,[],[f457])).
% 1.98/0.62  fof(f457,plain,(
% 1.98/0.62    $false | spl10_10),
% 1.98/0.62    inference(subsumption_resolution,[],[f456,f58])).
% 1.98/0.62  fof(f456,plain,(
% 1.98/0.62    ~v1_funct_1(sK5) | spl10_10),
% 1.98/0.62    inference(subsumption_resolution,[],[f453,f286])).
% 1.98/0.62  fof(f286,plain,(
% 1.98/0.62    ~r1_partfun1(sK5,sK6) | spl10_10),
% 1.98/0.62    inference(avatar_component_clause,[],[f284])).
% 1.98/0.62  fof(f284,plain,(
% 1.98/0.62    spl10_10 <=> r1_partfun1(sK5,sK6)),
% 1.98/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.98/0.62  fof(f453,plain,(
% 1.98/0.62    r1_partfun1(sK5,sK6) | ~v1_funct_1(sK5)),
% 1.98/0.62    inference(resolution,[],[f427,f110])).
% 1.98/0.62  fof(f427,plain,(
% 1.98/0.62    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | r1_partfun1(X5,sK6) | ~v1_funct_1(X5)) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f424,f60])).
% 1.98/0.64  % (16785)Refutation not found, incomplete strategy% (16785)------------------------------
% 1.98/0.64  % (16785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  fof(f424,plain,(
% 1.98/0.64    ( ! [X5] : (r1_partfun1(X5,sK6) | ~v1_funct_1(sK6) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,k2_enumset1(sK4,sK4,sK4,sK4)))) | ~v1_funct_1(X5)) )),
% 1.98/0.64    inference(resolution,[],[f114,f108])).
% 1.98/0.64  fof(f114,plain,(
% 1.98/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | r1_partfun1(X2,X3) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 1.98/0.64    inference(definition_unfolding,[],[f90,f106,f106])).
% 1.98/0.64  fof(f90,plain,(
% 1.98/0.64    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f30])).
% 1.98/0.64  fof(f30,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 1.98/0.64    inference(flattening,[],[f29])).
% 1.98/0.64  fof(f29,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 1.98/0.64    inference(ennf_transformation,[],[f12])).
% 1.98/0.64  fof(f12,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).
% 1.98/0.64  fof(f383,plain,(
% 1.98/0.64    ~spl10_6),
% 1.98/0.64    inference(avatar_contradiction_clause,[],[f382])).
% 1.98/0.64  fof(f382,plain,(
% 1.98/0.64    $false | ~spl10_6),
% 1.98/0.64    inference(subsumption_resolution,[],[f370,f64])).
% 1.98/0.64  fof(f370,plain,(
% 1.98/0.64    ~r1_tarski(k1_xboole_0,sK4) | ~spl10_6),
% 1.98/0.64    inference(superposition,[],[f152,f245])).
% 1.98/0.64  fof(f245,plain,(
% 1.98/0.64    k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) | ~spl10_6),
% 1.98/0.64    inference(avatar_component_clause,[],[f243])).
% 1.98/0.64  fof(f243,plain,(
% 1.98/0.64    spl10_6 <=> k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4)),
% 1.98/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.98/0.64  fof(f152,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X1,X2),X1)) )),
% 1.98/0.64    inference(resolution,[],[f149,f67])).
% 1.98/0.64  fof(f149,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))) )),
% 1.98/0.64    inference(resolution,[],[f133,f117])).
% 1.98/0.64  fof(f117,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.98/0.64    inference(definition_unfolding,[],[f91,f105])).
% 1.98/0.64  fof(f91,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f54])).
% 1.98/0.64  fof(f54,plain,(
% 1.98/0.64    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.98/0.64    inference(flattening,[],[f53])).
% 1.98/0.64  fof(f53,plain,(
% 1.98/0.64    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.98/0.64    inference(nnf_transformation,[],[f7])).
% 1.98/0.64  fof(f7,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.98/0.64  fof(f133,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,X0,X1,X2))) )),
% 1.98/0.64    inference(equality_resolution,[],[f120])).
% 1.98/0.64  fof(f120,plain,(
% 1.98/0.64    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X1,X1,X1,X2) != X3) )),
% 1.98/0.64    inference(definition_unfolding,[],[f102,f70,f105])).
% 1.98/0.64  fof(f102,plain,(
% 1.98/0.64    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k2_tarski(X1,X2) != X3) )),
% 1.98/0.64    inference(cnf_transformation,[],[f57])).
% 1.98/0.64  fof(f57,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.98/0.64    inference(flattening,[],[f56])).
% 1.98/0.64  fof(f56,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.98/0.64    inference(nnf_transformation,[],[f33])).
% 1.98/0.64  fof(f33,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.98/0.64    inference(ennf_transformation,[],[f6])).
% 1.98/0.64  fof(f6,axiom,(
% 1.98/0.64    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.98/0.64  fof(f291,plain,(
% 1.98/0.64    ~spl10_10 | spl10_11 | ~spl10_3 | ~spl10_5),
% 1.98/0.64    inference(avatar_split_clause,[],[f282,f239,f211,f288,f284])).
% 1.98/0.64  fof(f239,plain,(
% 1.98/0.64    spl10_5 <=> v1_partfun1(sK6,sK3)),
% 1.98/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.98/0.64  fof(f282,plain,(
% 1.98/0.64    r2_hidden(sK6,k1_xboole_0) | ~r1_partfun1(sK5,sK6) | (~spl10_3 | ~spl10_5)),
% 1.98/0.64    inference(resolution,[],[f229,f264])).
% 1.98/0.64  fof(f264,plain,(
% 1.98/0.64    ( ! [X0] : (sP0(X0,sK3,sK6,k2_enumset1(sK4,sK4,sK4,sK4)) | ~r1_partfun1(X0,sK6)) ) | ~spl10_5),
% 1.98/0.64    inference(subsumption_resolution,[],[f263,f60])).
% 1.98/0.64  fof(f263,plain,(
% 1.98/0.64    ( ! [X0] : (~r1_partfun1(X0,sK6) | sP0(X0,sK3,sK6,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK6)) ) | ~spl10_5),
% 1.98/0.64    inference(subsumption_resolution,[],[f260,f241])).
% 1.98/0.64  fof(f241,plain,(
% 1.98/0.64    v1_partfun1(sK6,sK3) | ~spl10_5),
% 1.98/0.64    inference(avatar_component_clause,[],[f239])).
% 1.98/0.64  fof(f260,plain,(
% 1.98/0.64    ( ! [X0] : (~r1_partfun1(X0,sK6) | ~v1_partfun1(sK6,sK3) | sP0(X0,sK3,sK6,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK6)) )),
% 1.98/0.64    inference(resolution,[],[f129,f108])).
% 1.98/0.64  fof(f129,plain,(
% 1.98/0.64    ( ! [X4,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | sP0(X0,X1,X4,X3) | ~v1_funct_1(X4)) )),
% 1.98/0.64    inference(equality_resolution,[],[f88])).
% 1.98/0.64  fof(f88,plain,(
% 1.98/0.64    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f52])).
% 1.98/0.64  fof(f52,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & ((r1_partfun1(X0,sK9(X0,X1,X2,X3)) & v1_partfun1(sK9(X0,X1,X2,X3),X1) & sK9(X0,X1,X2,X3) = X2 & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK9(X0,X1,X2,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.98/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f51])).
% 1.98/0.64  fof(f51,plain,(
% 1.98/0.64    ! [X3,X2,X1,X0] : (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) => (r1_partfun1(X0,sK9(X0,X1,X2,X3)) & v1_partfun1(sK9(X0,X1,X2,X3),X1) & sK9(X0,X1,X2,X3) = X2 & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK9(X0,X1,X2,X3))))),
% 1.98/0.64    introduced(choice_axiom,[])).
% 1.98/0.64  fof(f50,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 1.98/0.64    inference(rectify,[],[f49])).
% 1.98/0.64  fof(f49,plain,(
% 1.98/0.64    ! [X2,X0,X4,X1] : ((sP0(X2,X0,X4,X1) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~sP0(X2,X0,X4,X1)))),
% 1.98/0.64    inference(nnf_transformation,[],[f34])).
% 1.98/0.64  fof(f229,plain,(
% 1.98/0.64    ( ! [X0] : (~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) | r2_hidden(X0,k1_xboole_0)) ) | ~spl10_3),
% 1.98/0.64    inference(subsumption_resolution,[],[f226,f166])).
% 1.98/0.64  fof(f226,plain,(
% 1.98/0.64    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP0(sK5,sK3,X0,k2_enumset1(sK4,sK4,sK4,sK4)) | ~sP2(sK5,sK3,k2_enumset1(sK4,sK4,sK4,sK4))) ) | ~spl10_3),
% 1.98/0.64    inference(superposition,[],[f168,f213])).
% 1.98/0.64  fof(f213,plain,(
% 1.98/0.64    k1_xboole_0 = k5_partfun1(sK3,k2_enumset1(sK4,sK4,sK4,sK4),sK5) | ~spl10_3),
% 1.98/0.64    inference(avatar_component_clause,[],[f211])).
% 1.98/0.64  fof(f246,plain,(
% 1.98/0.64    spl10_5 | spl10_6),
% 1.98/0.64    inference(avatar_split_clause,[],[f237,f243,f239])).
% 1.98/0.64  fof(f237,plain,(
% 1.98/0.64    k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) | v1_partfun1(sK6,sK3)),
% 1.98/0.64    inference(subsumption_resolution,[],[f236,f60])).
% 1.98/0.64  fof(f236,plain,(
% 1.98/0.64    k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) | v1_partfun1(sK6,sK3) | ~v1_funct_1(sK6)),
% 1.98/0.64    inference(subsumption_resolution,[],[f233,f109])).
% 1.98/0.64  fof(f233,plain,(
% 1.98/0.64    k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) | v1_partfun1(sK6,sK3) | ~v1_funct_2(sK6,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK6)),
% 1.98/0.64    inference(resolution,[],[f140,f108])).
% 1.98/0.64  fof(f140,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.98/0.64    inference(duplicate_literal_removal,[],[f72])).
% 1.98/0.64  fof(f72,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f24])).
% 1.98/0.64  fof(f24,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.98/0.64    inference(flattening,[],[f23])).
% 1.98/0.64  fof(f23,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.98/0.64    inference(ennf_transformation,[],[f11])).
% 1.98/0.64  fof(f11,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 1.98/0.64  % SZS output end Proof for theBenchmark
% 1.98/0.64  % (16791)------------------------------
% 1.98/0.64  % (16791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (16791)Termination reason: Refutation
% 1.98/0.64  
% 1.98/0.64  % (16791)Memory used [KB]: 11897
% 1.98/0.64  % (16791)Time elapsed: 0.229 s
% 1.98/0.64  % (16791)------------------------------
% 1.98/0.64  % (16791)------------------------------
% 1.98/0.64  % (16784)Success in time 0.286 s
%------------------------------------------------------------------------------
