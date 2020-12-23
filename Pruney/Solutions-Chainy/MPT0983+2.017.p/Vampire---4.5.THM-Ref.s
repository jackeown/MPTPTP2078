%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 352 expanded)
%              Number of leaves         :   45 ( 136 expanded)
%              Depth                    :   11
%              Number of atoms          :  639 (1836 expanded)
%              Number of equality atoms :   65 (  83 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f562,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f131,f135,f142,f263,f266,f321,f326,f329,f332,f373,f395,f413,f415,f417,f426,f430,f435,f445,f452,f456,f535,f539,f561])).

fof(f561,plain,
    ( spl6_3
    | ~ spl6_16
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | spl6_3
    | ~ spl6_16
    | ~ spl6_28 ),
    inference(resolution,[],[f556,f465])).

fof(f465,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl6_3 ),
    inference(resolution,[],[f464,f64])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f464,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | ~ r1_tarski(sK2,X2) )
    | spl6_3 ),
    inference(resolution,[],[f461,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
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

fof(f461,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2),X0)
        | ~ r1_tarski(sK2,X0) )
    | spl6_3 ),
    inference(resolution,[],[f460,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f460,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | spl6_3 ),
    inference(resolution,[],[f122,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f122,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f556,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl6_16
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f548,f101])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f548,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl6_16
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f385,f530])).

fof(f530,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl6_28
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f385,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl6_16
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f539,plain,(
    spl6_29 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | spl6_29 ),
    inference(resolution,[],[f534,f97])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f68,f65])).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f534,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl6_29
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f535,plain,
    ( spl6_28
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_29
    | ~ spl6_8
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f526,f433,f260,f532,f318,f314,f528])).

fof(f314,plain,
    ( spl6_12
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f318,plain,
    ( spl6_13
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f260,plain,
    ( spl6_8
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f433,plain,
    ( spl6_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f526,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ spl6_8
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f525,f262])).

fof(f262,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f260])).

fof(f525,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ spl6_23 ),
    inference(resolution,[],[f434,f60])).

fof(f60,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f434,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,sK1,X0)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0 )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f433])).

fof(f456,plain,(
    spl6_25 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | spl6_25 ),
    inference(resolution,[],[f447,f61])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

% (30254)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f447,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl6_25 ),
    inference(resolution,[],[f444,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f444,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl6_25
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f452,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | spl6_24 ),
    inference(resolution,[],[f446,f61])).

fof(f446,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_24 ),
    inference(resolution,[],[f440,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f440,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl6_24
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f445,plain,
    ( ~ spl6_24
    | ~ spl6_25
    | spl6_2
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f436,f420,f110,f442,f438])).

fof(f110,plain,
    ( spl6_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f420,plain,
    ( spl6_22
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f436,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_22 ),
    inference(superposition,[],[f99,f421])).

fof(f421,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f420])).

fof(f99,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f435,plain,
    ( ~ spl6_11
    | spl6_23
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f431,f371,f433,f310])).

fof(f310,plain,
    ( spl6_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f371,plain,
    ( spl6_15
  <=> ! [X1,X3,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f431,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) )
    | ~ spl6_15 ),
    inference(resolution,[],[f372,f57])).

fof(f57,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f372,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,X1,X2)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f371])).

fof(f430,plain,
    ( ~ spl6_13
    | spl6_22
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f428,f406,f420,f318])).

fof(f406,plain,
    ( spl6_20
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f428,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_20 ),
    inference(superposition,[],[f86,f408])).

fof(f408,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f406])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f426,plain,
    ( ~ spl6_8
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl6_8
    | spl6_21 ),
    inference(resolution,[],[f412,f333])).

fof(f333,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f62,f262])).

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f412,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl6_21
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f417,plain,(
    spl6_19 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl6_19 ),
    inference(resolution,[],[f404,f57])).

fof(f404,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl6_19
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f415,plain,(
    spl6_18 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | spl6_18 ),
    inference(resolution,[],[f400,f60])).

fof(f400,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl6_18
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f413,plain,
    ( ~ spl6_12
    | ~ spl6_18
    | ~ spl6_13
    | ~ spl6_5
    | ~ spl6_19
    | ~ spl6_11
    | spl6_20
    | ~ spl6_21
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f396,f260,f410,f406,f310,f402,f128,f318,f398,f314])).

fof(f128,plain,
    ( spl6_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f396,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl6_8 ),
    inference(superposition,[],[f89,f262])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f395,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl6_16 ),
    inference(resolution,[],[f392,f58])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f392,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_16 ),
    inference(resolution,[],[f384,f80])).

% (30246)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f384,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f383])).

fof(f373,plain,
    ( ~ spl6_5
    | spl6_15
    | spl6_1 ),
    inference(avatar_split_clause,[],[f369,f106,f371,f128])).

fof(f106,plain,
    ( spl6_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f369,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 = X0
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(X3,X2,X0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ v1_funct_1(sK2) )
    | spl6_1 ),
    inference(resolution,[],[f90,f108])).

fof(f108,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f332,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl6_13 ),
    inference(resolution,[],[f320,f61])).

fof(f320,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f318])).

fof(f329,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl6_11 ),
    inference(resolution,[],[f312,f58])).

fof(f312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f310])).

fof(f326,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl6_12 ),
    inference(resolution,[],[f316,f59])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f316,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f314])).

fof(f321,plain,
    ( ~ spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_6 ),
    inference(avatar_split_clause,[],[f306,f252,f318,f314,f310,f128])).

fof(f252,plain,
    ( spl6_6
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f306,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_6 ),
    inference(resolution,[],[f95,f254])).

fof(f254,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f252])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f266,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f258,f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f258,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl6_7
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f263,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f248,f260,f256,f252])).

fof(f248,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f92,f62])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f142,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl6_4 ),
    inference(resolution,[],[f137,f58])).

fof(f137,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_4 ),
    inference(resolution,[],[f85,f126])).

fof(f126,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f135,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f130,f56])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f130,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f131,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f118,f106,f128,f124,f120])).

fof(f118,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(sK2)
    | spl6_1 ),
    inference(resolution,[],[f72,f108])).

fof(f72,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f113,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f63,f110,f106])).

fof(f63,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:13:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30241)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (30242)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (30257)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (30240)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (30248)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (30244)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (30249)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (30253)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (30258)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (30245)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (30250)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (30261)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (30259)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (30238)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (30252)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (30265)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (30264)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (30251)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (30239)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (30237)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (30243)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (30266)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (30249)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (30256)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  % (30260)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.55  % (30247)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (30263)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.55  % (30255)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.56  % (30259)Refutation not found, incomplete strategy% (30259)------------------------------
% 1.40/0.56  % (30259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (30259)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (30259)Memory used [KB]: 11001
% 1.40/0.56  % (30259)Time elapsed: 0.098 s
% 1.40/0.56  % (30259)------------------------------
% 1.40/0.56  % (30259)------------------------------
% 1.40/0.56  % (30262)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.56  % SZS output start Proof for theBenchmark
% 1.40/0.56  fof(f562,plain,(
% 1.40/0.56    $false),
% 1.40/0.56    inference(avatar_sat_refutation,[],[f113,f131,f135,f142,f263,f266,f321,f326,f329,f332,f373,f395,f413,f415,f417,f426,f430,f435,f445,f452,f456,f535,f539,f561])).
% 1.40/0.56  fof(f561,plain,(
% 1.40/0.56    spl6_3 | ~spl6_16 | ~spl6_28),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f559])).
% 1.40/0.56  fof(f559,plain,(
% 1.40/0.56    $false | (spl6_3 | ~spl6_16 | ~spl6_28)),
% 1.40/0.56    inference(resolution,[],[f556,f465])).
% 1.40/0.56  fof(f465,plain,(
% 1.40/0.56    ~r1_tarski(sK2,k1_xboole_0) | spl6_3),
% 1.40/0.56    inference(resolution,[],[f464,f64])).
% 1.40/0.56  fof(f64,plain,(
% 1.40/0.56    v1_xboole_0(k1_xboole_0)),
% 1.40/0.56    inference(cnf_transformation,[],[f3])).
% 1.40/0.56  fof(f3,axiom,(
% 1.40/0.56    v1_xboole_0(k1_xboole_0)),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.40/0.56  fof(f464,plain,(
% 1.40/0.56    ( ! [X2] : (~v1_xboole_0(X2) | ~r1_tarski(sK2,X2)) ) | spl6_3),
% 1.40/0.56    inference(resolution,[],[f461,f73])).
% 1.40/0.56  fof(f73,plain,(
% 1.40/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f46,plain,(
% 1.40/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 1.40/0.56  fof(f45,plain,(
% 1.40/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f44,plain,(
% 1.40/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.56    inference(rectify,[],[f43])).
% 1.40/0.56  fof(f43,plain,(
% 1.40/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.56    inference(nnf_transformation,[],[f1])).
% 1.40/0.56  fof(f1,axiom,(
% 1.40/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.40/0.56  fof(f461,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(sK4(sK2),X0) | ~r1_tarski(sK2,X0)) ) | spl6_3),
% 1.40/0.56    inference(resolution,[],[f460,f77])).
% 1.40/0.56  fof(f77,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f51])).
% 1.40/0.56  fof(f51,plain,(
% 1.40/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 1.40/0.56  fof(f50,plain,(
% 1.40/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f49,plain,(
% 1.40/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.56    inference(rectify,[],[f48])).
% 1.40/0.56  fof(f48,plain,(
% 1.40/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.56    inference(nnf_transformation,[],[f28])).
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f2])).
% 1.40/0.56  fof(f2,axiom,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.56  fof(f460,plain,(
% 1.40/0.56    r2_hidden(sK4(sK2),sK2) | spl6_3),
% 1.40/0.56    inference(resolution,[],[f122,f74])).
% 1.40/0.56  fof(f74,plain,(
% 1.40/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f122,plain,(
% 1.40/0.56    ~v1_xboole_0(sK2) | spl6_3),
% 1.40/0.56    inference(avatar_component_clause,[],[f120])).
% 1.40/0.56  fof(f120,plain,(
% 1.40/0.56    spl6_3 <=> v1_xboole_0(sK2)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.40/0.56  fof(f556,plain,(
% 1.40/0.56    r1_tarski(sK2,k1_xboole_0) | (~spl6_16 | ~spl6_28)),
% 1.40/0.56    inference(forward_demodulation,[],[f548,f101])).
% 1.40/0.56  fof(f101,plain,(
% 1.40/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.40/0.56    inference(equality_resolution,[],[f83])).
% 1.40/0.56  fof(f83,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f54])).
% 1.40/0.56  fof(f54,plain,(
% 1.40/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.40/0.56    inference(flattening,[],[f53])).
% 1.40/0.56  fof(f53,plain,(
% 1.40/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.40/0.56    inference(nnf_transformation,[],[f4])).
% 1.40/0.56  fof(f4,axiom,(
% 1.40/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.40/0.56  fof(f548,plain,(
% 1.40/0.56    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl6_16 | ~spl6_28)),
% 1.40/0.56    inference(backward_demodulation,[],[f385,f530])).
% 1.40/0.56  fof(f530,plain,(
% 1.40/0.56    k1_xboole_0 = sK0 | ~spl6_28),
% 1.40/0.56    inference(avatar_component_clause,[],[f528])).
% 1.40/0.56  fof(f528,plain,(
% 1.40/0.56    spl6_28 <=> k1_xboole_0 = sK0),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.40/0.56  fof(f385,plain,(
% 1.40/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl6_16),
% 1.40/0.56    inference(avatar_component_clause,[],[f383])).
% 1.40/0.56  fof(f383,plain,(
% 1.40/0.56    spl6_16 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.40/0.56  fof(f539,plain,(
% 1.40/0.56    spl6_29),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f536])).
% 1.40/0.56  fof(f536,plain,(
% 1.40/0.56    $false | spl6_29),
% 1.40/0.56    inference(resolution,[],[f534,f97])).
% 1.40/0.56  fof(f97,plain,(
% 1.40/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.40/0.56    inference(definition_unfolding,[],[f68,f65])).
% 1.40/0.56  fof(f65,plain,(
% 1.40/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f16])).
% 1.40/0.56  fof(f16,axiom,(
% 1.40/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.40/0.56  fof(f68,plain,(
% 1.40/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f8])).
% 1.40/0.56  fof(f8,axiom,(
% 1.40/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.40/0.56  fof(f534,plain,(
% 1.40/0.56    ~v2_funct_1(k6_partfun1(sK0)) | spl6_29),
% 1.40/0.56    inference(avatar_component_clause,[],[f532])).
% 1.40/0.56  fof(f532,plain,(
% 1.40/0.56    spl6_29 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.40/0.56  fof(f535,plain,(
% 1.40/0.56    spl6_28 | ~spl6_12 | ~spl6_13 | ~spl6_29 | ~spl6_8 | ~spl6_23),
% 1.40/0.56    inference(avatar_split_clause,[],[f526,f433,f260,f532,f318,f314,f528])).
% 1.40/0.56  fof(f314,plain,(
% 1.40/0.56    spl6_12 <=> v1_funct_1(sK3)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.40/0.56  fof(f318,plain,(
% 1.40/0.56    spl6_13 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.40/0.56  fof(f260,plain,(
% 1.40/0.56    spl6_8 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.40/0.56  fof(f433,plain,(
% 1.40/0.56    spl6_23 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.40/0.56  fof(f526,plain,(
% 1.40/0.56    ~v2_funct_1(k6_partfun1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK0 | (~spl6_8 | ~spl6_23)),
% 1.40/0.56    inference(forward_demodulation,[],[f525,f262])).
% 1.40/0.56  fof(f262,plain,(
% 1.40/0.56    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl6_8),
% 1.40/0.56    inference(avatar_component_clause,[],[f260])).
% 1.40/0.56  fof(f525,plain,(
% 1.40/0.56    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK0 | ~spl6_23),
% 1.40/0.56    inference(resolution,[],[f434,f60])).
% 1.40/0.56  fof(f60,plain,(
% 1.40/0.56    v1_funct_2(sK3,sK1,sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f42])).
% 1.40/0.56  fof(f42,plain,(
% 1.40/0.56    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41,f40])).
% 1.40/0.56  fof(f40,plain,(
% 1.40/0.56    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f41,plain,(
% 1.40/0.56    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.57  fof(f22,plain,(
% 1.40/0.57    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.40/0.57    inference(flattening,[],[f21])).
% 1.40/0.57  fof(f21,plain,(
% 1.40/0.57    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.40/0.57    inference(ennf_transformation,[],[f20])).
% 1.40/0.57  fof(f20,negated_conjecture,(
% 1.40/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.40/0.57    inference(negated_conjecture,[],[f19])).
% 1.40/0.57  fof(f19,conjecture,(
% 1.40/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.40/0.57  fof(f434,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~v1_funct_2(X1,sK1,X0) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | k1_xboole_0 = X0) ) | ~spl6_23),
% 1.40/0.57    inference(avatar_component_clause,[],[f433])).
% 1.40/0.57  fof(f456,plain,(
% 1.40/0.57    spl6_25),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f453])).
% 1.40/0.57  fof(f453,plain,(
% 1.40/0.57    $false | spl6_25),
% 1.40/0.57    inference(resolution,[],[f447,f61])).
% 1.40/0.57  fof(f61,plain,(
% 1.40/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.40/0.57    inference(cnf_transformation,[],[f42])).
% 1.40/0.57  % (30254)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.57  fof(f447,plain,(
% 1.40/0.57    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl6_25),
% 1.40/0.57    inference(resolution,[],[f444,f88])).
% 1.40/0.57  fof(f88,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f31])).
% 1.40/0.57  fof(f31,plain,(
% 1.40/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.57    inference(ennf_transformation,[],[f10])).
% 1.40/0.57  fof(f10,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.40/0.57  fof(f444,plain,(
% 1.40/0.57    ~v5_relat_1(sK3,sK0) | spl6_25),
% 1.40/0.57    inference(avatar_component_clause,[],[f442])).
% 1.40/0.57  fof(f442,plain,(
% 1.40/0.57    spl6_25 <=> v5_relat_1(sK3,sK0)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.40/0.57  fof(f452,plain,(
% 1.40/0.57    spl6_24),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f448])).
% 1.40/0.57  fof(f448,plain,(
% 1.40/0.57    $false | spl6_24),
% 1.40/0.57    inference(resolution,[],[f446,f61])).
% 1.40/0.57  fof(f446,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_24),
% 1.40/0.57    inference(resolution,[],[f440,f85])).
% 1.40/0.57  fof(f85,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f29])).
% 1.40/0.57  fof(f29,plain,(
% 1.40/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.57    inference(ennf_transformation,[],[f9])).
% 1.40/0.57  fof(f9,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.40/0.57  fof(f440,plain,(
% 1.40/0.57    ~v1_relat_1(sK3) | spl6_24),
% 1.40/0.57    inference(avatar_component_clause,[],[f438])).
% 1.40/0.57  fof(f438,plain,(
% 1.40/0.57    spl6_24 <=> v1_relat_1(sK3)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.40/0.57  fof(f445,plain,(
% 1.40/0.57    ~spl6_24 | ~spl6_25 | spl6_2 | ~spl6_22),
% 1.40/0.57    inference(avatar_split_clause,[],[f436,f420,f110,f442,f438])).
% 1.40/0.57  fof(f110,plain,(
% 1.40/0.57    spl6_2 <=> v2_funct_2(sK3,sK0)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.40/0.57  fof(f420,plain,(
% 1.40/0.57    spl6_22 <=> sK0 = k2_relat_1(sK3)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.40/0.57  fof(f436,plain,(
% 1.40/0.57    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl6_22),
% 1.40/0.57    inference(superposition,[],[f99,f421])).
% 1.40/0.57  fof(f421,plain,(
% 1.40/0.57    sK0 = k2_relat_1(sK3) | ~spl6_22),
% 1.40/0.57    inference(avatar_component_clause,[],[f420])).
% 1.40/0.57  fof(f99,plain,(
% 1.40/0.57    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.40/0.57    inference(equality_resolution,[],[f76])).
% 1.40/0.57  fof(f76,plain,(
% 1.40/0.57    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f47])).
% 1.40/0.57  fof(f47,plain,(
% 1.40/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.57    inference(nnf_transformation,[],[f27])).
% 1.40/0.57  fof(f27,plain,(
% 1.40/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.57    inference(flattening,[],[f26])).
% 1.40/0.57  fof(f26,plain,(
% 1.40/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.40/0.57    inference(ennf_transformation,[],[f14])).
% 1.40/0.57  fof(f14,axiom,(
% 1.40/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.40/0.57  fof(f435,plain,(
% 1.40/0.57    ~spl6_11 | spl6_23 | ~spl6_15),
% 1.40/0.57    inference(avatar_split_clause,[],[f431,f371,f433,f310])).
% 1.40/0.57  fof(f310,plain,(
% 1.40/0.57    spl6_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.40/0.57  fof(f371,plain,(
% 1.40/0.57    spl6_15 <=> ! [X1,X3,X0,X2] : (k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)))),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.40/0.57  fof(f431,plain,(
% 1.40/0.57    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))) ) | ~spl6_15),
% 1.40/0.57    inference(resolution,[],[f372,f57])).
% 1.40/0.57  fof(f57,plain,(
% 1.40/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.40/0.57    inference(cnf_transformation,[],[f42])).
% 1.40/0.57  fof(f372,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK2,X1,X2) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3))) ) | ~spl6_15),
% 1.40/0.57    inference(avatar_component_clause,[],[f371])).
% 1.40/0.57  fof(f430,plain,(
% 1.40/0.57    ~spl6_13 | spl6_22 | ~spl6_20),
% 1.40/0.57    inference(avatar_split_clause,[],[f428,f406,f420,f318])).
% 1.40/0.57  fof(f406,plain,(
% 1.40/0.57    spl6_20 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.40/0.57  fof(f428,plain,(
% 1.40/0.57    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_20),
% 1.40/0.57    inference(superposition,[],[f86,f408])).
% 1.40/0.57  fof(f408,plain,(
% 1.40/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl6_20),
% 1.40/0.57    inference(avatar_component_clause,[],[f406])).
% 1.40/0.57  fof(f86,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f30])).
% 1.40/0.57  fof(f30,plain,(
% 1.40/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.57    inference(ennf_transformation,[],[f11])).
% 1.40/0.57  fof(f11,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.40/0.57  fof(f426,plain,(
% 1.40/0.57    ~spl6_8 | spl6_21),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f424])).
% 1.40/0.57  fof(f424,plain,(
% 1.40/0.57    $false | (~spl6_8 | spl6_21)),
% 1.40/0.57    inference(resolution,[],[f412,f333])).
% 1.40/0.57  fof(f333,plain,(
% 1.40/0.57    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl6_8),
% 1.40/0.57    inference(backward_demodulation,[],[f62,f262])).
% 1.40/0.57  fof(f62,plain,(
% 1.40/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.40/0.57    inference(cnf_transformation,[],[f42])).
% 1.40/0.57  fof(f412,plain,(
% 1.40/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl6_21),
% 1.40/0.57    inference(avatar_component_clause,[],[f410])).
% 1.40/0.57  fof(f410,plain,(
% 1.40/0.57    spl6_21 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.40/0.57  fof(f417,plain,(
% 1.40/0.57    spl6_19),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f416])).
% 1.40/0.57  fof(f416,plain,(
% 1.40/0.57    $false | spl6_19),
% 1.40/0.57    inference(resolution,[],[f404,f57])).
% 1.40/0.57  fof(f404,plain,(
% 1.40/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl6_19),
% 1.40/0.57    inference(avatar_component_clause,[],[f402])).
% 1.40/0.57  fof(f402,plain,(
% 1.40/0.57    spl6_19 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.40/0.57  fof(f415,plain,(
% 1.40/0.57    spl6_18),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f414])).
% 1.40/0.57  fof(f414,plain,(
% 1.40/0.57    $false | spl6_18),
% 1.40/0.57    inference(resolution,[],[f400,f60])).
% 1.40/0.57  fof(f400,plain,(
% 1.40/0.57    ~v1_funct_2(sK3,sK1,sK0) | spl6_18),
% 1.40/0.57    inference(avatar_component_clause,[],[f398])).
% 1.40/0.57  fof(f398,plain,(
% 1.40/0.57    spl6_18 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.40/0.57  fof(f413,plain,(
% 1.40/0.57    ~spl6_12 | ~spl6_18 | ~spl6_13 | ~spl6_5 | ~spl6_19 | ~spl6_11 | spl6_20 | ~spl6_21 | ~spl6_8),
% 1.40/0.57    inference(avatar_split_clause,[],[f396,f260,f410,f406,f310,f402,f128,f318,f398,f314])).
% 1.40/0.57  fof(f128,plain,(
% 1.40/0.57    spl6_5 <=> v1_funct_1(sK2)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.40/0.57  fof(f396,plain,(
% 1.40/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl6_8),
% 1.40/0.57    inference(superposition,[],[f89,f262])).
% 1.40/0.57  fof(f89,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f33])).
% 1.40/0.57  fof(f33,plain,(
% 1.40/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.40/0.57    inference(flattening,[],[f32])).
% 1.40/0.57  fof(f32,plain,(
% 1.40/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.40/0.57    inference(ennf_transformation,[],[f17])).
% 1.40/0.57  fof(f17,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.40/0.57  fof(f395,plain,(
% 1.40/0.57    spl6_16),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f393])).
% 1.40/0.57  fof(f393,plain,(
% 1.40/0.57    $false | spl6_16),
% 1.40/0.57    inference(resolution,[],[f392,f58])).
% 1.40/0.57  fof(f58,plain,(
% 1.40/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.40/0.57    inference(cnf_transformation,[],[f42])).
% 1.40/0.57  fof(f392,plain,(
% 1.40/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_16),
% 1.40/0.57    inference(resolution,[],[f384,f80])).
% 1.40/0.57  % (30246)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.57  fof(f80,plain,(
% 1.40/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f52])).
% 1.40/0.57  fof(f52,plain,(
% 1.40/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.40/0.57    inference(nnf_transformation,[],[f5])).
% 1.40/0.57  fof(f5,axiom,(
% 1.40/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.40/0.57  fof(f384,plain,(
% 1.40/0.57    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | spl6_16),
% 1.40/0.57    inference(avatar_component_clause,[],[f383])).
% 1.40/0.57  fof(f373,plain,(
% 1.40/0.57    ~spl6_5 | spl6_15 | spl6_1),
% 1.40/0.57    inference(avatar_split_clause,[],[f369,f106,f371,f128])).
% 1.40/0.57  fof(f106,plain,(
% 1.40/0.57    spl6_1 <=> v2_funct_1(sK2)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.40/0.57  fof(f369,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | ~v1_funct_1(sK2)) ) | spl6_1),
% 1.40/0.57    inference(resolution,[],[f90,f108])).
% 1.40/0.57  fof(f108,plain,(
% 1.40/0.57    ~v2_funct_1(sK2) | spl6_1),
% 1.40/0.57    inference(avatar_component_clause,[],[f106])).
% 1.40/0.57  fof(f90,plain,(
% 1.40/0.57    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f35])).
% 1.40/0.57  fof(f35,plain,(
% 1.40/0.57    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.40/0.57    inference(flattening,[],[f34])).
% 1.40/0.57  fof(f34,plain,(
% 1.40/0.57    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.40/0.57    inference(ennf_transformation,[],[f18])).
% 1.40/0.57  fof(f18,axiom,(
% 1.40/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.40/0.57  fof(f332,plain,(
% 1.40/0.57    spl6_13),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f330])).
% 1.40/0.57  fof(f330,plain,(
% 1.40/0.57    $false | spl6_13),
% 1.40/0.57    inference(resolution,[],[f320,f61])).
% 1.40/0.57  fof(f320,plain,(
% 1.40/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_13),
% 1.40/0.57    inference(avatar_component_clause,[],[f318])).
% 1.40/0.57  fof(f329,plain,(
% 1.40/0.57    spl6_11),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f327])).
% 1.40/0.57  fof(f327,plain,(
% 1.40/0.57    $false | spl6_11),
% 1.40/0.57    inference(resolution,[],[f312,f58])).
% 1.40/0.57  fof(f312,plain,(
% 1.40/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_11),
% 1.40/0.57    inference(avatar_component_clause,[],[f310])).
% 1.40/0.57  fof(f326,plain,(
% 1.40/0.57    spl6_12),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f324])).
% 1.40/0.57  fof(f324,plain,(
% 1.40/0.57    $false | spl6_12),
% 1.40/0.57    inference(resolution,[],[f316,f59])).
% 1.40/0.57  fof(f59,plain,(
% 1.40/0.57    v1_funct_1(sK3)),
% 1.40/0.57    inference(cnf_transformation,[],[f42])).
% 1.40/0.57  fof(f316,plain,(
% 1.40/0.57    ~v1_funct_1(sK3) | spl6_12),
% 1.40/0.57    inference(avatar_component_clause,[],[f314])).
% 1.40/0.57  fof(f321,plain,(
% 1.40/0.57    ~spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | spl6_6),
% 1.40/0.57    inference(avatar_split_clause,[],[f306,f252,f318,f314,f310,f128])).
% 1.40/0.57  fof(f252,plain,(
% 1.40/0.57    spl6_6 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.40/0.57  fof(f306,plain,(
% 1.40/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_6),
% 1.40/0.57    inference(resolution,[],[f95,f254])).
% 1.40/0.57  fof(f254,plain,(
% 1.40/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_6),
% 1.40/0.57    inference(avatar_component_clause,[],[f252])).
% 1.40/0.57  fof(f95,plain,(
% 1.40/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f39])).
% 1.40/0.57  fof(f39,plain,(
% 1.40/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.40/0.57    inference(flattening,[],[f38])).
% 1.40/0.57  fof(f38,plain,(
% 1.40/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.40/0.57    inference(ennf_transformation,[],[f15])).
% 1.40/0.57  fof(f15,axiom,(
% 1.40/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.40/0.57  fof(f266,plain,(
% 1.40/0.57    spl6_7),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f264])).
% 1.40/0.57  fof(f264,plain,(
% 1.40/0.57    $false | spl6_7),
% 1.40/0.57    inference(resolution,[],[f258,f96])).
% 1.40/0.57  fof(f96,plain,(
% 1.40/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.40/0.57    inference(definition_unfolding,[],[f66,f65])).
% 1.40/0.57  fof(f66,plain,(
% 1.40/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f13])).
% 1.40/0.57  fof(f13,axiom,(
% 1.40/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.40/0.57  fof(f258,plain,(
% 1.40/0.57    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_7),
% 1.40/0.57    inference(avatar_component_clause,[],[f256])).
% 1.40/0.57  fof(f256,plain,(
% 1.40/0.57    spl6_7 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.40/0.57  fof(f263,plain,(
% 1.40/0.57    ~spl6_6 | ~spl6_7 | spl6_8),
% 1.40/0.57    inference(avatar_split_clause,[],[f248,f260,f256,f252])).
% 1.40/0.57  fof(f248,plain,(
% 1.40/0.57    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.40/0.57    inference(resolution,[],[f92,f62])).
% 1.40/0.57  fof(f92,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f55])).
% 1.40/0.57  fof(f55,plain,(
% 1.40/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.57    inference(nnf_transformation,[],[f37])).
% 1.40/0.57  fof(f37,plain,(
% 1.40/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.57    inference(flattening,[],[f36])).
% 1.40/0.57  fof(f36,plain,(
% 1.40/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.40/0.57    inference(ennf_transformation,[],[f12])).
% 1.40/0.57  fof(f12,axiom,(
% 1.40/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.40/0.57  fof(f142,plain,(
% 1.40/0.57    spl6_4),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f138])).
% 1.40/0.57  fof(f138,plain,(
% 1.40/0.57    $false | spl6_4),
% 1.40/0.57    inference(resolution,[],[f137,f58])).
% 1.40/0.57  fof(f137,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_4),
% 1.40/0.57    inference(resolution,[],[f85,f126])).
% 1.40/0.57  fof(f126,plain,(
% 1.40/0.57    ~v1_relat_1(sK2) | spl6_4),
% 1.40/0.57    inference(avatar_component_clause,[],[f124])).
% 1.40/0.57  fof(f124,plain,(
% 1.40/0.57    spl6_4 <=> v1_relat_1(sK2)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.40/0.57  fof(f135,plain,(
% 1.40/0.57    spl6_5),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f133])).
% 1.40/0.57  fof(f133,plain,(
% 1.40/0.57    $false | spl6_5),
% 1.40/0.57    inference(resolution,[],[f130,f56])).
% 1.40/0.57  fof(f56,plain,(
% 1.40/0.57    v1_funct_1(sK2)),
% 1.40/0.57    inference(cnf_transformation,[],[f42])).
% 1.40/0.57  fof(f130,plain,(
% 1.40/0.57    ~v1_funct_1(sK2) | spl6_5),
% 1.40/0.57    inference(avatar_component_clause,[],[f128])).
% 1.40/0.57  fof(f131,plain,(
% 1.40/0.57    ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_1),
% 1.40/0.57    inference(avatar_split_clause,[],[f118,f106,f128,f124,f120])).
% 1.40/0.57  fof(f118,plain,(
% 1.40/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_xboole_0(sK2) | spl6_1),
% 1.40/0.57    inference(resolution,[],[f72,f108])).
% 1.40/0.57  fof(f72,plain,(
% 1.40/0.57    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f25])).
% 1.40/0.57  fof(f25,plain,(
% 1.40/0.57    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.40/0.57    inference(flattening,[],[f24])).
% 1.40/0.57  fof(f24,plain,(
% 1.40/0.57    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 1.40/0.57    inference(ennf_transformation,[],[f7])).
% 1.40/0.57  fof(f7,axiom,(
% 1.40/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).
% 1.40/0.57  fof(f113,plain,(
% 1.40/0.57    ~spl6_1 | ~spl6_2),
% 1.40/0.57    inference(avatar_split_clause,[],[f63,f110,f106])).
% 1.40/0.57  fof(f63,plain,(
% 1.40/0.57    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.40/0.57    inference(cnf_transformation,[],[f42])).
% 1.40/0.57  % SZS output end Proof for theBenchmark
% 1.40/0.57  % (30249)------------------------------
% 1.40/0.57  % (30249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (30249)Termination reason: Refutation
% 1.40/0.57  
% 1.40/0.57  % (30249)Memory used [KB]: 6396
% 1.40/0.57  % (30249)Time elapsed: 0.135 s
% 1.40/0.57  % (30249)------------------------------
% 1.40/0.57  % (30249)------------------------------
% 1.40/0.57  % (30254)Refutation not found, incomplete strategy% (30254)------------------------------
% 1.40/0.57  % (30254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (30236)Success in time 0.202 s
%------------------------------------------------------------------------------
