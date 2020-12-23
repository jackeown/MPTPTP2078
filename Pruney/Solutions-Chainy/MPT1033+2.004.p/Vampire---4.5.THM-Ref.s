%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 312 expanded)
%              Number of leaves         :   23 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  404 (1857 expanded)
%              Number of equality atoms :   73 ( 383 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f738,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f172,f177,f594,f612,f688,f693,f697,f727,f737])).

fof(f737,plain,
    ( ~ spl9_8
    | spl9_44 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | ~ spl9_8
    | spl9_44 ),
    inference(subsumption_resolution,[],[f734,f166])).

fof(f166,plain,
    ( v1_xboole_0(sK3)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl9_8
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f734,plain,
    ( ~ v1_xboole_0(sK3)
    | spl9_44 ),
    inference(resolution,[],[f683,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f121,f114])).

fof(f114,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
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

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( sP0(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f20,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f121,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f86,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f683,plain,
    ( ~ r1_tarski(sK3,sK4)
    | spl9_44 ),
    inference(avatar_component_clause,[],[f681])).

fof(f681,plain,
    ( spl9_44
  <=> r1_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f727,plain,
    ( ~ spl9_45
    | spl9_24
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f721,f674,f528,f685])).

fof(f685,plain,
    ( spl9_45
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f528,plain,
    ( spl9_24
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f674,plain,
    ( spl9_43
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f721,plain,
    ( sK3 != sK4
    | spl9_24
    | ~ spl9_43 ),
    inference(backward_demodulation,[],[f529,f676])).

fof(f676,plain,
    ( sK3 = sK5
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f674])).

fof(f529,plain,
    ( sK4 != sK5
    | spl9_24 ),
    inference(avatar_component_clause,[],[f528])).

fof(f697,plain,
    ( spl9_43
    | ~ spl9_9
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f696,f670,f169,f674])).

fof(f169,plain,
    ( spl9_9
  <=> r1_tarski(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f670,plain,
    ( spl9_42
  <=> r1_tarski(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f696,plain,
    ( sK3 = sK5
    | ~ spl9_9
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f694,f171])).

fof(f171,plain,
    ( r1_tarski(sK5,sK3)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f694,plain,
    ( sK3 = sK5
    | ~ r1_tarski(sK5,sK3)
    | ~ spl9_42 ),
    inference(resolution,[],[f671,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f671,plain,
    ( r1_tarski(sK3,sK5)
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f670])).

% (17144)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f693,plain,
    ( ~ spl9_8
    | spl9_42 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | ~ spl9_8
    | spl9_42 ),
    inference(subsumption_resolution,[],[f690,f166])).

fof(f690,plain,
    ( ~ v1_xboole_0(sK3)
    | spl9_42 ),
    inference(resolution,[],[f672,f124])).

fof(f672,plain,
    ( ~ r1_tarski(sK3,sK5)
    | spl9_42 ),
    inference(avatar_component_clause,[],[f670])).

fof(f688,plain,
    ( ~ spl9_44
    | spl9_45
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f678,f174,f685,f681])).

fof(f174,plain,
    ( spl9_10
  <=> r1_tarski(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f678,plain,
    ( sK3 = sK4
    | ~ r1_tarski(sK3,sK4)
    | ~ spl9_10 ),
    inference(resolution,[],[f176,f85])).

fof(f176,plain,
    ( r1_tarski(sK4,sK3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f612,plain,(
    ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f599,f438])).

fof(f438,plain,(
    r2_relset_1(sK2,sK3,sK4,sK4) ),
    inference(resolution,[],[f103,f60])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5)
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_partfun1(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK2,sK3,sK4,X3)
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & r1_partfun1(sK4,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK2,sK3,sK4,X3)
        & ( k1_xboole_0 = sK2
          | k1_xboole_0 != sK3 )
        & r1_partfun1(sK4,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_2(X3,sK2,sK3)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK2,sK3,sK4,sK5)
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & r1_partfun1(sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f599,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK4)
    | ~ spl9_24 ),
    inference(backward_demodulation,[],[f66,f530])).

fof(f530,plain,
    ( sK4 = sK5
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f528])).

fof(f66,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f594,plain,
    ( spl9_24
    | spl9_8 ),
    inference(avatar_split_clause,[],[f593,f165,f528])).

fof(f593,plain,
    ( sK4 = sK5
    | spl9_8 ),
    inference(subsumption_resolution,[],[f592,f58])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f592,plain,
    ( sK4 = sK5
    | ~ v1_funct_1(sK4)
    | spl9_8 ),
    inference(subsumption_resolution,[],[f591,f64])).

fof(f64,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f591,plain,
    ( sK4 = sK5
    | ~ r1_partfun1(sK4,sK5)
    | ~ v1_funct_1(sK4)
    | spl9_8 ),
    inference(subsumption_resolution,[],[f582,f474])).

fof(f474,plain,
    ( v1_partfun1(sK4,sK2)
    | spl9_8 ),
    inference(subsumption_resolution,[],[f473,f167])).

fof(f167,plain,
    ( ~ v1_xboole_0(sK3)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f473,plain,
    ( v1_partfun1(sK4,sK2)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f472,f58])).

fof(f472,plain,
    ( ~ v1_funct_1(sK4)
    | v1_partfun1(sK4,sK2)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f460,f59])).

fof(f59,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f460,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | v1_partfun1(sK4,sK2)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f76,f60])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f582,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | sK4 = sK5
    | ~ r1_partfun1(sK4,sK5)
    | ~ v1_funct_1(sK4)
    | spl9_8 ),
    inference(resolution,[],[f506,f60])).

fof(f506,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_partfun1(X1,sK2)
        | sK5 = X1
        | ~ r1_partfun1(X1,sK5)
        | ~ v1_funct_1(X1) )
    | spl9_8 ),
    inference(subsumption_resolution,[],[f505,f61])).

fof(f61,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f505,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK5)
        | ~ v1_partfun1(X1,sK2)
        | sK5 = X1
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_1(X1) )
    | spl9_8 ),
    inference(subsumption_resolution,[],[f492,f477])).

fof(f477,plain,
    ( v1_partfun1(sK5,sK2)
    | spl9_8 ),
    inference(subsumption_resolution,[],[f476,f167])).

fof(f476,plain,
    ( v1_partfun1(sK5,sK2)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f475,f61])).

fof(f475,plain,
    ( ~ v1_funct_1(sK5)
    | v1_partfun1(sK5,sK2)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f461,f62])).

fof(f62,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f461,plain,
    ( ~ v1_funct_2(sK5,sK2,sK3)
    | ~ v1_funct_1(sK5)
    | v1_partfun1(sK5,sK2)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f76,f63])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f492,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK5)
      | ~ v1_partfun1(sK5,sK2)
      | ~ v1_partfun1(X1,sK2)
      | sK5 = X1
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f94,f63])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

% (17137)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (17147)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f177,plain,
    ( ~ spl9_8
    | spl9_10 ),
    inference(avatar_split_clause,[],[f159,f174,f165])).

fof(f159,plain,
    ( r1_tarski(sK4,sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(superposition,[],[f119,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X1,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f101,f114])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f119,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f86,f60])).

fof(f172,plain,
    ( ~ spl9_8
    | spl9_9 ),
    inference(avatar_split_clause,[],[f158,f169,f165])).

fof(f158,plain,
    ( r1_tarski(sK5,sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(superposition,[],[f120,f117])).

fof(f120,plain,(
    r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f86,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (17139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (17140)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (17140)Refutation not found, incomplete strategy% (17140)------------------------------
% 0.22/0.51  % (17140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17148)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (17140)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17140)Memory used [KB]: 6140
% 0.22/0.52  % (17140)Time elapsed: 0.089 s
% 0.22/0.52  % (17140)------------------------------
% 0.22/0.52  % (17140)------------------------------
% 0.22/0.52  % (17156)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (17150)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (17136)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (17141)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (17143)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (17141)Refutation not found, incomplete strategy% (17141)------------------------------
% 0.22/0.53  % (17141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17141)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17141)Memory used [KB]: 10618
% 0.22/0.53  % (17141)Time elapsed: 0.112 s
% 0.22/0.53  % (17141)------------------------------
% 0.22/0.53  % (17141)------------------------------
% 0.22/0.53  % (17136)Refutation not found, incomplete strategy% (17136)------------------------------
% 0.22/0.53  % (17136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17136)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17136)Memory used [KB]: 10746
% 0.22/0.53  % (17136)Time elapsed: 0.113 s
% 0.22/0.53  % (17136)------------------------------
% 0.22/0.53  % (17136)------------------------------
% 0.22/0.53  % (17149)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (17151)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (17135)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (17157)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (17139)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f738,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f172,f177,f594,f612,f688,f693,f697,f727,f737])).
% 0.22/0.54  fof(f737,plain,(
% 0.22/0.54    ~spl9_8 | spl9_44),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f736])).
% 0.22/0.54  fof(f736,plain,(
% 0.22/0.54    $false | (~spl9_8 | spl9_44)),
% 0.22/0.54    inference(subsumption_resolution,[],[f734,f166])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    v1_xboole_0(sK3) | ~spl9_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f165])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    spl9_8 <=> v1_xboole_0(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.54  fof(f734,plain,(
% 0.22/0.54    ~v1_xboole_0(sK3) | spl9_44),
% 0.22/0.54    inference(resolution,[],[f683,f124])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(superposition,[],[f121,f114])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f72,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(rectify,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0] : ((sP0(sK7(X0),X0) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK7(X0),X0) & r2_hidden(sK7(X0),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(definition_folding,[],[f20,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f86,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f683,plain,(
% 0.22/0.54    ~r1_tarski(sK3,sK4) | spl9_44),
% 0.22/0.54    inference(avatar_component_clause,[],[f681])).
% 0.22/0.54  fof(f681,plain,(
% 0.22/0.54    spl9_44 <=> r1_tarski(sK3,sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 0.22/0.54  fof(f727,plain,(
% 0.22/0.54    ~spl9_45 | spl9_24 | ~spl9_43),
% 0.22/0.54    inference(avatar_split_clause,[],[f721,f674,f528,f685])).
% 0.22/0.54  fof(f685,plain,(
% 0.22/0.54    spl9_45 <=> sK3 = sK4),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 0.22/0.54  fof(f528,plain,(
% 0.22/0.54    spl9_24 <=> sK4 = sK5),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.22/0.54  fof(f674,plain,(
% 0.22/0.54    spl9_43 <=> sK3 = sK5),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.22/0.54  fof(f721,plain,(
% 0.22/0.54    sK3 != sK4 | (spl9_24 | ~spl9_43)),
% 0.22/0.54    inference(backward_demodulation,[],[f529,f676])).
% 0.22/0.54  fof(f676,plain,(
% 0.22/0.54    sK3 = sK5 | ~spl9_43),
% 0.22/0.54    inference(avatar_component_clause,[],[f674])).
% 0.22/0.54  fof(f529,plain,(
% 0.22/0.54    sK4 != sK5 | spl9_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f528])).
% 0.22/0.54  fof(f697,plain,(
% 0.22/0.54    spl9_43 | ~spl9_9 | ~spl9_42),
% 0.22/0.54    inference(avatar_split_clause,[],[f696,f670,f169,f674])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    spl9_9 <=> r1_tarski(sK5,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.54  fof(f670,plain,(
% 0.22/0.54    spl9_42 <=> r1_tarski(sK3,sK5)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 0.22/0.54  fof(f696,plain,(
% 0.22/0.54    sK3 = sK5 | (~spl9_9 | ~spl9_42)),
% 0.22/0.54    inference(subsumption_resolution,[],[f694,f171])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    r1_tarski(sK5,sK3) | ~spl9_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f169])).
% 0.22/0.54  fof(f694,plain,(
% 0.22/0.54    sK3 = sK5 | ~r1_tarski(sK5,sK3) | ~spl9_42),
% 0.22/0.54    inference(resolution,[],[f671,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f671,plain,(
% 0.22/0.54    r1_tarski(sK3,sK5) | ~spl9_42),
% 0.22/0.54    inference(avatar_component_clause,[],[f670])).
% 0.22/0.54  % (17144)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  fof(f693,plain,(
% 0.22/0.54    ~spl9_8 | spl9_42),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f692])).
% 0.22/0.54  fof(f692,plain,(
% 0.22/0.54    $false | (~spl9_8 | spl9_42)),
% 0.22/0.54    inference(subsumption_resolution,[],[f690,f166])).
% 0.22/0.54  fof(f690,plain,(
% 0.22/0.54    ~v1_xboole_0(sK3) | spl9_42),
% 0.22/0.54    inference(resolution,[],[f672,f124])).
% 0.22/0.54  fof(f672,plain,(
% 0.22/0.54    ~r1_tarski(sK3,sK5) | spl9_42),
% 0.22/0.54    inference(avatar_component_clause,[],[f670])).
% 0.22/0.54  fof(f688,plain,(
% 0.22/0.54    ~spl9_44 | spl9_45 | ~spl9_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f678,f174,f685,f681])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl9_10 <=> r1_tarski(sK4,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.54  fof(f678,plain,(
% 0.22/0.54    sK3 = sK4 | ~r1_tarski(sK3,sK4) | ~spl9_10),
% 0.22/0.54    inference(resolution,[],[f176,f85])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    r1_tarski(sK4,sK3) | ~spl9_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f174])).
% 0.22/0.54  fof(f612,plain,(
% 0.22/0.54    ~spl9_24),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f611])).
% 0.22/0.54  fof(f611,plain,(
% 0.22/0.54    $false | ~spl9_24),
% 0.22/0.54    inference(subsumption_resolution,[],[f599,f438])).
% 0.22/0.54  fof(f438,plain,(
% 0.22/0.54    r2_relset_1(sK2,sK3,sK4,sK4)),
% 0.22/0.54    inference(resolution,[],[f103,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    (~r2_relset_1(sK2,sK3,sK4,sK5) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f39,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) => (~r2_relset_1(sK2,sK3,sK4,sK5) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f16])).
% 0.22/0.54  fof(f16,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.54    inference(condensation,[],[f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.54  fof(f599,plain,(
% 0.22/0.54    ~r2_relset_1(sK2,sK3,sK4,sK4) | ~spl9_24),
% 0.22/0.54    inference(backward_demodulation,[],[f66,f530])).
% 0.22/0.54  fof(f530,plain,(
% 0.22/0.54    sK4 = sK5 | ~spl9_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f528])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f594,plain,(
% 0.22/0.54    spl9_24 | spl9_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f593,f165,f528])).
% 0.22/0.54  fof(f593,plain,(
% 0.22/0.54    sK4 = sK5 | spl9_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f592,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    v1_funct_1(sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f592,plain,(
% 0.22/0.54    sK4 = sK5 | ~v1_funct_1(sK4) | spl9_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f591,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    r1_partfun1(sK4,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f591,plain,(
% 0.22/0.54    sK4 = sK5 | ~r1_partfun1(sK4,sK5) | ~v1_funct_1(sK4) | spl9_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f582,f474])).
% 0.22/0.54  fof(f474,plain,(
% 0.22/0.54    v1_partfun1(sK4,sK2) | spl9_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f473,f167])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ~v1_xboole_0(sK3) | spl9_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f165])).
% 0.22/0.54  fof(f473,plain,(
% 0.22/0.54    v1_partfun1(sK4,sK2) | v1_xboole_0(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f472,f58])).
% 0.22/0.54  fof(f472,plain,(
% 0.22/0.54    ~v1_funct_1(sK4) | v1_partfun1(sK4,sK2) | v1_xboole_0(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f460,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    v1_funct_2(sK4,sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f460,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4) | v1_partfun1(sK4,sK2) | v1_xboole_0(sK3)),
% 0.22/0.54    inference(resolution,[],[f76,f60])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.54  fof(f582,plain,(
% 0.22/0.54    ~v1_partfun1(sK4,sK2) | sK4 = sK5 | ~r1_partfun1(sK4,sK5) | ~v1_funct_1(sK4) | spl9_8),
% 0.22/0.54    inference(resolution,[],[f506,f60])).
% 0.22/0.54  fof(f506,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_partfun1(X1,sK2) | sK5 = X1 | ~r1_partfun1(X1,sK5) | ~v1_funct_1(X1)) ) | spl9_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f505,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    v1_funct_1(sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f505,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_partfun1(X1,sK5) | ~v1_partfun1(X1,sK2) | sK5 = X1 | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(X1)) ) | spl9_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f492,f477])).
% 0.22/0.54  fof(f477,plain,(
% 0.22/0.54    v1_partfun1(sK5,sK2) | spl9_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f476,f167])).
% 0.22/0.54  fof(f476,plain,(
% 0.22/0.54    v1_partfun1(sK5,sK2) | v1_xboole_0(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f475,f61])).
% 0.22/0.54  fof(f475,plain,(
% 0.22/0.54    ~v1_funct_1(sK5) | v1_partfun1(sK5,sK2) | v1_xboole_0(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f461,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    v1_funct_2(sK5,sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f461,plain,(
% 0.22/0.54    ~v1_funct_2(sK5,sK2,sK3) | ~v1_funct_1(sK5) | v1_partfun1(sK5,sK2) | v1_xboole_0(sK3)),
% 0.22/0.54    inference(resolution,[],[f76,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f492,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_partfun1(X1,sK5) | ~v1_partfun1(sK5,sK2) | ~v1_partfun1(X1,sK2) | sK5 = X1 | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f94,f63])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  % (17137)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (17147)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ~spl9_8 | spl9_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f159,f174,f165])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    r1_tarski(sK4,sK3) | ~v1_xboole_0(sK3)),
% 0.22/0.54    inference(superposition,[],[f119,f117])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X1,X0) = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(superposition,[],[f101,f114])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.54    inference(flattening,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))),
% 0.22/0.54    inference(resolution,[],[f86,f60])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ~spl9_8 | spl9_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f158,f169,f165])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    r1_tarski(sK5,sK3) | ~v1_xboole_0(sK3)),
% 0.22/0.54    inference(superposition,[],[f120,f117])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    r1_tarski(sK5,k2_zfmisc_1(sK2,sK3))),
% 0.22/0.54    inference(resolution,[],[f86,f63])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (17139)------------------------------
% 0.22/0.54  % (17139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17139)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (17139)Memory used [KB]: 6396
% 0.22/0.54  % (17139)Time elapsed: 0.120 s
% 0.22/0.54  % (17139)------------------------------
% 0.22/0.54  % (17139)------------------------------
% 0.22/0.55  % (17134)Success in time 0.183 s
%------------------------------------------------------------------------------
