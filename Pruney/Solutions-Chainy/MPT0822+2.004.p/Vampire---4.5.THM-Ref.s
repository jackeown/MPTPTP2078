%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 298 expanded)
%              Number of leaves         :   24 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  366 (1255 expanded)
%              Number of equality atoms :   46 ( 228 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f70,f111,f177,f202,f208,f213,f231,f238,f306])).

fof(f306,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f266,f65])).

fof(f65,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f266,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f246,f252])).

fof(f252,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f71,f59])).

fof(f59,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl9_2
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f71,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ! [X5] :
          ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
            | ~ r2_hidden(X5,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
        & r2_hidden(X3,sK1) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
     => r2_hidden(k4_tarski(sK4(X5),X5),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f246,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f56,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl9_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f238,plain,
    ( ~ spl9_5
    | spl9_7 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl9_5
    | spl9_7 ),
    inference(resolution,[],[f235,f34])).

fof(f235,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl9_5
    | spl9_7 ),
    inference(resolution,[],[f234,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f234,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ spl9_5
    | spl9_7 ),
    inference(subsumption_resolution,[],[f232,f102])).

fof(f102,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f232,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl9_7 ),
    inference(resolution,[],[f139,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f139,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl9_7
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f231,plain,
    ( spl9_2
    | spl9_9
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl9_2
    | spl9_9
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f229,f172])).

fof(f172,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),sK1)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl9_9
  <=> r2_hidden(sK6(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f229,plain,
    ( r2_hidden(sK6(sK2,sK1),sK1)
    | spl9_2
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f227,f72])).

fof(f72,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl9_2 ),
    inference(superposition,[],[f60,f71])).

fof(f60,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f227,plain,
    ( sK1 = k2_relat_1(sK2)
    | r2_hidden(sK6(sK2,sK1),sK1)
    | ~ spl9_10 ),
    inference(resolution,[],[f176,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f176,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl9_10
  <=> ! [X4] : ~ r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f213,plain,(
    spl9_13 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl9_13 ),
    inference(subsumption_resolution,[],[f210,f201])).

fof(f201,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl9_13
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f210,plain,
    ( r1_tarski(sK1,sK1)
    | spl9_13 ),
    inference(resolution,[],[f209,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f209,plain,
    ( ~ r2_hidden(sK5(sK1,sK1),sK1)
    | spl9_13 ),
    inference(resolution,[],[f201,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f208,plain,
    ( ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f203,f173])).

fof(f173,plain,
    ( r2_hidden(sK6(sK2,sK1),sK1)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f203,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),sK1)
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(resolution,[],[f176,f69])).

fof(f69,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f202,plain,
    ( ~ spl9_13
    | spl9_10
    | spl9_2
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f197,f171,f58,f175,f199])).

fof(f197,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(X3,sK6(sK2,sK1)),sK2)
        | ~ r1_tarski(sK1,sK1) )
    | spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f190,f72])).

fof(f190,plain,
    ( ! [X3] :
        ( sK1 = k2_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X3,sK6(sK2,sK1)),sK2)
        | ~ r1_tarski(sK1,sK1) )
    | ~ spl9_9 ),
    inference(resolution,[],[f173,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK6(X1,X2),X3)
      | k2_relat_1(X1) = X2
      | ~ r2_hidden(k4_tarski(X0,sK6(X1,X2)),X1)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f177,plain,
    ( spl9_9
    | spl9_10
    | spl9_2
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f169,f138,f58,f175,f171])).

fof(f169,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2)
        | r2_hidden(sK6(sK2,sK1),sK1) )
    | spl9_2
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f168,f72])).

fof(f168,plain,
    ( ! [X4] :
        ( sK1 = k2_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2)
        | r2_hidden(sK6(sK2,sK1),sK1) )
    | ~ spl9_7 ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ! [X4] :
        ( sK1 = k2_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2)
        | sK1 = k2_relat_1(sK2)
        | r2_hidden(sK6(sK2,sK1),sK1) )
    | ~ spl9_7 ),
    inference(resolution,[],[f163,f47])).

fof(f163,plain,
    ( ! [X12,X10,X11] :
        ( ~ r2_hidden(k4_tarski(X12,sK6(X11,sK1)),sK2)
        | sK1 = k2_relat_1(X11)
        | ~ r2_hidden(k4_tarski(X10,sK6(X11,sK1)),X11) )
    | ~ spl9_7 ),
    inference(resolution,[],[f76,f140])).

fof(f140,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f76,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_tarski(k2_relat_1(X8),X6)
      | ~ r2_hidden(k4_tarski(X7,sK6(X5,X6)),X5)
      | k2_relat_1(X5) = X6
      | ~ r2_hidden(k4_tarski(X9,sK6(X5,X6)),X8) ) ),
    inference(resolution,[],[f73,f52])).

fof(f52,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl9_5 ),
    inference(subsumption_resolution,[],[f109,f39])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f109,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_5 ),
    inference(resolution,[],[f108,f34])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl9_5 ),
    inference(resolution,[],[f103,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f103,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f70,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f35,f58,f68])).

fof(f35,plain,(
    ! [X5] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | r2_hidden(k4_tarski(sK4(X5),X5),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f36,f58,f63])).

fof(f36,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f37,f58,f55])).

fof(f37,plain,(
    ! [X4] :
      ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (12872)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (12893)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (12885)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (12898)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (12876)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (12883)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (12874)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (12890)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (12870)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (12871)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (12884)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (12899)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (12874)Refutation not found, incomplete strategy% (12874)------------------------------
% 0.20/0.53  % (12874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12874)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12874)Memory used [KB]: 6268
% 0.20/0.53  % (12874)Time elapsed: 0.104 s
% 0.20/0.53  % (12874)------------------------------
% 0.20/0.53  % (12874)------------------------------
% 0.20/0.53  % (12886)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (12887)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (12889)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (12879)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (12875)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (12872)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (12869)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (12895)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (12878)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (12881)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (12877)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (12896)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (12880)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (12892)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (12880)Refutation not found, incomplete strategy% (12880)------------------------------
% 1.41/0.55  % (12880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (12880)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (12880)Memory used [KB]: 10618
% 1.41/0.55  % (12880)Time elapsed: 0.141 s
% 1.41/0.55  % (12880)------------------------------
% 1.41/0.55  % (12880)------------------------------
% 1.41/0.55  % (12900)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (12888)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (12888)Refutation not found, incomplete strategy% (12888)------------------------------
% 1.41/0.55  % (12888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (12888)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (12888)Memory used [KB]: 10618
% 1.41/0.55  % (12888)Time elapsed: 0.150 s
% 1.41/0.55  % (12888)------------------------------
% 1.41/0.55  % (12888)------------------------------
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f308,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(avatar_sat_refutation,[],[f61,f66,f70,f111,f177,f202,f208,f213,f231,f238,f306])).
% 1.41/0.56  fof(f306,plain,(
% 1.41/0.56    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f305])).
% 1.41/0.56  fof(f305,plain,(
% 1.41/0.56    $false | (~spl9_1 | ~spl9_2 | ~spl9_3)),
% 1.41/0.56    inference(subsumption_resolution,[],[f266,f65])).
% 1.41/0.56  fof(f65,plain,(
% 1.41/0.56    r2_hidden(sK3,sK1) | ~spl9_3),
% 1.41/0.56    inference(avatar_component_clause,[],[f63])).
% 1.41/0.56  fof(f63,plain,(
% 1.41/0.56    spl9_3 <=> r2_hidden(sK3,sK1)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.41/0.56  fof(f266,plain,(
% 1.41/0.56    ~r2_hidden(sK3,sK1) | (~spl9_1 | ~spl9_2)),
% 1.41/0.56    inference(backward_demodulation,[],[f246,f252])).
% 1.41/0.56  fof(f252,plain,(
% 1.41/0.56    sK1 = k2_relat_1(sK2) | ~spl9_2),
% 1.41/0.56    inference(backward_demodulation,[],[f71,f59])).
% 1.41/0.56  fof(f59,plain,(
% 1.41/0.56    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl9_2),
% 1.41/0.56    inference(avatar_component_clause,[],[f58])).
% 1.41/0.56  fof(f58,plain,(
% 1.41/0.56    spl9_2 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.41/0.56  fof(f71,plain,(
% 1.41/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.41/0.56    inference(resolution,[],[f49,f34])).
% 1.41/0.56  fof(f34,plain,(
% 1.41/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    (sK1 != k2_relset_1(sK0,sK1,sK2) | (! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2) & r2_hidden(sK3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f21,f20,f19])).
% 1.41/0.56  fof(f19,plain,(
% 1.41/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK2) & r2_hidden(X3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK2) & r2_hidden(X3,sK1)) => (! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2) & r2_hidden(sK3,sK1))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f21,plain,(
% 1.41/0.56    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK2) => r2_hidden(k4_tarski(sK4(X5),X5),sK2))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f18,plain,(
% 1.41/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(rectify,[],[f17])).
% 1.41/0.56  fof(f17,plain,(
% 1.41/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(flattening,[],[f16])).
% 1.41/0.56  fof(f16,plain,(
% 1.41/0.56    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(nnf_transformation,[],[f10])).
% 1.41/0.56  fof(f10,plain,(
% 1.41/0.56    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(ennf_transformation,[],[f9])).
% 1.41/0.56  fof(f9,negated_conjecture,(
% 1.41/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.41/0.56    inference(negated_conjecture,[],[f8])).
% 1.41/0.56  fof(f8,conjecture,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 1.41/0.56  fof(f49,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f14])).
% 1.41/0.56  fof(f14,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(ennf_transformation,[],[f7])).
% 1.41/0.56  fof(f7,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.41/0.56  fof(f246,plain,(
% 1.41/0.56    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~spl9_1),
% 1.41/0.56    inference(resolution,[],[f56,f53])).
% 1.41/0.56  fof(f53,plain,(
% 1.41/0.56    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.41/0.56    inference(equality_resolution,[],[f45])).
% 1.41/0.56  fof(f45,plain,(
% 1.41/0.56    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f33])).
% 1.41/0.56  fof(f33,plain,(
% 1.41/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f31,plain,(
% 1.41/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.41/0.56    inference(rectify,[],[f28])).
% 1.41/0.56  fof(f28,plain,(
% 1.41/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.41/0.56    inference(nnf_transformation,[],[f4])).
% 1.41/0.56  fof(f4,axiom,(
% 1.41/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.41/0.56  fof(f56,plain,(
% 1.41/0.56    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2)) ) | ~spl9_1),
% 1.41/0.56    inference(avatar_component_clause,[],[f55])).
% 1.41/0.56  fof(f55,plain,(
% 1.41/0.56    spl9_1 <=> ! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.41/0.56  fof(f238,plain,(
% 1.41/0.56    ~spl9_5 | spl9_7),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f237])).
% 1.41/0.56  fof(f237,plain,(
% 1.41/0.56    $false | (~spl9_5 | spl9_7)),
% 1.41/0.56    inference(resolution,[],[f235,f34])).
% 1.41/0.56  fof(f235,plain,(
% 1.41/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl9_5 | spl9_7)),
% 1.41/0.56    inference(resolution,[],[f234,f51])).
% 1.41/0.56  fof(f51,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(ennf_transformation,[],[f6])).
% 1.41/0.56  fof(f6,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.41/0.56  fof(f234,plain,(
% 1.41/0.56    ~v5_relat_1(sK2,sK1) | (~spl9_5 | spl9_7)),
% 1.41/0.56    inference(subsumption_resolution,[],[f232,f102])).
% 1.41/0.56  fof(f102,plain,(
% 1.41/0.56    v1_relat_1(sK2) | ~spl9_5),
% 1.41/0.56    inference(avatar_component_clause,[],[f101])).
% 1.41/0.56  fof(f101,plain,(
% 1.41/0.56    spl9_5 <=> v1_relat_1(sK2)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.41/0.56  fof(f232,plain,(
% 1.41/0.56    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl9_7),
% 1.41/0.56    inference(resolution,[],[f139,f40])).
% 1.41/0.56  fof(f40,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f23,plain,(
% 1.41/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.41/0.56    inference(nnf_transformation,[],[f12])).
% 1.41/0.56  fof(f12,plain,(
% 1.41/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.41/0.56    inference(ennf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.41/0.56  fof(f139,plain,(
% 1.41/0.56    ~r1_tarski(k2_relat_1(sK2),sK1) | spl9_7),
% 1.41/0.56    inference(avatar_component_clause,[],[f138])).
% 1.41/0.56  fof(f138,plain,(
% 1.41/0.56    spl9_7 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.41/0.56  fof(f231,plain,(
% 1.41/0.56    spl9_2 | spl9_9 | ~spl9_10),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f230])).
% 1.41/0.56  fof(f230,plain,(
% 1.41/0.56    $false | (spl9_2 | spl9_9 | ~spl9_10)),
% 1.41/0.56    inference(subsumption_resolution,[],[f229,f172])).
% 1.41/0.56  fof(f172,plain,(
% 1.41/0.56    ~r2_hidden(sK6(sK2,sK1),sK1) | spl9_9),
% 1.41/0.56    inference(avatar_component_clause,[],[f171])).
% 1.41/0.56  fof(f171,plain,(
% 1.41/0.56    spl9_9 <=> r2_hidden(sK6(sK2,sK1),sK1)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.41/0.56  fof(f229,plain,(
% 1.41/0.56    r2_hidden(sK6(sK2,sK1),sK1) | (spl9_2 | ~spl9_10)),
% 1.41/0.56    inference(subsumption_resolution,[],[f227,f72])).
% 1.41/0.56  fof(f72,plain,(
% 1.41/0.56    sK1 != k2_relat_1(sK2) | spl9_2),
% 1.41/0.56    inference(superposition,[],[f60,f71])).
% 1.41/0.56  fof(f60,plain,(
% 1.41/0.56    sK1 != k2_relset_1(sK0,sK1,sK2) | spl9_2),
% 1.41/0.56    inference(avatar_component_clause,[],[f58])).
% 1.41/0.56  fof(f227,plain,(
% 1.41/0.56    sK1 = k2_relat_1(sK2) | r2_hidden(sK6(sK2,sK1),sK1) | ~spl9_10),
% 1.41/0.56    inference(resolution,[],[f176,f47])).
% 1.41/0.56  fof(f47,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f33])).
% 1.41/0.56  fof(f176,plain,(
% 1.41/0.56    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2)) ) | ~spl9_10),
% 1.41/0.56    inference(avatar_component_clause,[],[f175])).
% 1.41/0.56  fof(f175,plain,(
% 1.41/0.56    spl9_10 <=> ! [X4] : ~r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.41/0.56  fof(f213,plain,(
% 1.41/0.56    spl9_13),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f212])).
% 1.41/0.56  fof(f212,plain,(
% 1.41/0.56    $false | spl9_13),
% 1.41/0.56    inference(subsumption_resolution,[],[f210,f201])).
% 1.41/0.56  fof(f201,plain,(
% 1.41/0.56    ~r1_tarski(sK1,sK1) | spl9_13),
% 1.41/0.56    inference(avatar_component_clause,[],[f199])).
% 1.41/0.56  fof(f199,plain,(
% 1.41/0.56    spl9_13 <=> r1_tarski(sK1,sK1)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.41/0.56  fof(f210,plain,(
% 1.41/0.56    r1_tarski(sK1,sK1) | spl9_13),
% 1.41/0.56    inference(resolution,[],[f209,f43])).
% 1.41/0.56  fof(f43,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  fof(f27,plain,(
% 1.41/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 1.41/0.56  fof(f26,plain,(
% 1.41/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f25,plain,(
% 1.41/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.56    inference(rectify,[],[f24])).
% 1.41/0.56  fof(f24,plain,(
% 1.41/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.56    inference(nnf_transformation,[],[f13])).
% 1.41/0.56  fof(f13,plain,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.56  fof(f209,plain,(
% 1.41/0.56    ~r2_hidden(sK5(sK1,sK1),sK1) | spl9_13),
% 1.41/0.56    inference(resolution,[],[f201,f44])).
% 1.41/0.56  fof(f44,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  fof(f208,plain,(
% 1.41/0.56    ~spl9_4 | ~spl9_9 | ~spl9_10),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f207])).
% 1.41/0.56  fof(f207,plain,(
% 1.41/0.56    $false | (~spl9_4 | ~spl9_9 | ~spl9_10)),
% 1.41/0.56    inference(subsumption_resolution,[],[f203,f173])).
% 1.41/0.56  fof(f173,plain,(
% 1.41/0.56    r2_hidden(sK6(sK2,sK1),sK1) | ~spl9_9),
% 1.41/0.56    inference(avatar_component_clause,[],[f171])).
% 1.41/0.56  fof(f203,plain,(
% 1.41/0.56    ~r2_hidden(sK6(sK2,sK1),sK1) | (~spl9_4 | ~spl9_10)),
% 1.41/0.56    inference(resolution,[],[f176,f69])).
% 1.41/0.56  fof(f69,plain,(
% 1.41/0.56    ( ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1)) ) | ~spl9_4),
% 1.41/0.56    inference(avatar_component_clause,[],[f68])).
% 1.41/0.56  fof(f68,plain,(
% 1.41/0.56    spl9_4 <=> ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.41/0.56  fof(f202,plain,(
% 1.41/0.56    ~spl9_13 | spl9_10 | spl9_2 | ~spl9_9),
% 1.41/0.56    inference(avatar_split_clause,[],[f197,f171,f58,f175,f199])).
% 1.41/0.56  fof(f197,plain,(
% 1.41/0.56    ( ! [X3] : (~r2_hidden(k4_tarski(X3,sK6(sK2,sK1)),sK2) | ~r1_tarski(sK1,sK1)) ) | (spl9_2 | ~spl9_9)),
% 1.41/0.56    inference(subsumption_resolution,[],[f190,f72])).
% 1.41/0.56  fof(f190,plain,(
% 1.41/0.56    ( ! [X3] : (sK1 = k2_relat_1(sK2) | ~r2_hidden(k4_tarski(X3,sK6(sK2,sK1)),sK2) | ~r1_tarski(sK1,sK1)) ) | ~spl9_9),
% 1.41/0.56    inference(resolution,[],[f173,f73])).
% 1.41/0.56  fof(f73,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK6(X1,X2),X3) | k2_relat_1(X1) = X2 | ~r2_hidden(k4_tarski(X0,sK6(X1,X2)),X1) | ~r1_tarski(X3,X2)) )),
% 1.41/0.56    inference(resolution,[],[f48,f42])).
% 1.41/0.56  fof(f42,plain,(
% 1.41/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  fof(f48,plain,(
% 1.41/0.56    ( ! [X0,X3,X1] : (~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | k2_relat_1(X0) = X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f33])).
% 1.41/0.56  fof(f177,plain,(
% 1.41/0.56    spl9_9 | spl9_10 | spl9_2 | ~spl9_7),
% 1.41/0.56    inference(avatar_split_clause,[],[f169,f138,f58,f175,f171])).
% 1.41/0.56  fof(f169,plain,(
% 1.41/0.56    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2) | r2_hidden(sK6(sK2,sK1),sK1)) ) | (spl9_2 | ~spl9_7)),
% 1.41/0.56    inference(subsumption_resolution,[],[f168,f72])).
% 1.41/0.56  fof(f168,plain,(
% 1.41/0.56    ( ! [X4] : (sK1 = k2_relat_1(sK2) | ~r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2) | r2_hidden(sK6(sK2,sK1),sK1)) ) | ~spl9_7),
% 1.41/0.56    inference(duplicate_literal_removal,[],[f166])).
% 1.41/0.56  fof(f166,plain,(
% 1.41/0.56    ( ! [X4] : (sK1 = k2_relat_1(sK2) | ~r2_hidden(k4_tarski(X4,sK6(sK2,sK1)),sK2) | sK1 = k2_relat_1(sK2) | r2_hidden(sK6(sK2,sK1),sK1)) ) | ~spl9_7),
% 1.41/0.56    inference(resolution,[],[f163,f47])).
% 1.41/0.56  fof(f163,plain,(
% 1.41/0.56    ( ! [X12,X10,X11] : (~r2_hidden(k4_tarski(X12,sK6(X11,sK1)),sK2) | sK1 = k2_relat_1(X11) | ~r2_hidden(k4_tarski(X10,sK6(X11,sK1)),X11)) ) | ~spl9_7),
% 1.41/0.56    inference(resolution,[],[f76,f140])).
% 1.41/0.56  fof(f140,plain,(
% 1.41/0.56    r1_tarski(k2_relat_1(sK2),sK1) | ~spl9_7),
% 1.41/0.56    inference(avatar_component_clause,[],[f138])).
% 1.41/0.56  fof(f76,plain,(
% 1.41/0.56    ( ! [X6,X8,X7,X5,X9] : (~r1_tarski(k2_relat_1(X8),X6) | ~r2_hidden(k4_tarski(X7,sK6(X5,X6)),X5) | k2_relat_1(X5) = X6 | ~r2_hidden(k4_tarski(X9,sK6(X5,X6)),X8)) )),
% 1.41/0.56    inference(resolution,[],[f73,f52])).
% 1.41/0.56  fof(f52,plain,(
% 1.41/0.56    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 1.41/0.56    inference(equality_resolution,[],[f46])).
% 1.41/0.56  fof(f46,plain,(
% 1.41/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f33])).
% 1.41/0.56  fof(f111,plain,(
% 1.41/0.56    spl9_5),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f110])).
% 1.41/0.56  fof(f110,plain,(
% 1.41/0.56    $false | spl9_5),
% 1.41/0.56    inference(subsumption_resolution,[],[f109,f39])).
% 1.41/0.56  fof(f39,plain,(
% 1.41/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.41/0.56  fof(f109,plain,(
% 1.41/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl9_5),
% 1.41/0.56    inference(resolution,[],[f108,f34])).
% 1.41/0.56  fof(f108,plain,(
% 1.41/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl9_5),
% 1.41/0.56    inference(resolution,[],[f103,f38])).
% 1.41/0.56  fof(f38,plain,(
% 1.41/0.56    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f11])).
% 1.41/0.56  fof(f11,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.56    inference(ennf_transformation,[],[f2])).
% 1.41/0.56  fof(f2,axiom,(
% 1.41/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.41/0.56  fof(f103,plain,(
% 1.41/0.56    ~v1_relat_1(sK2) | spl9_5),
% 1.41/0.56    inference(avatar_component_clause,[],[f101])).
% 1.41/0.56  fof(f70,plain,(
% 1.41/0.56    spl9_4 | spl9_2),
% 1.41/0.56    inference(avatar_split_clause,[],[f35,f58,f68])).
% 1.41/0.56  fof(f35,plain,(
% 1.41/0.56    ( ! [X5] : (sK1 = k2_relset_1(sK0,sK1,sK2) | r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f66,plain,(
% 1.41/0.56    spl9_3 | ~spl9_2),
% 1.41/0.56    inference(avatar_split_clause,[],[f36,f58,f63])).
% 1.41/0.56  fof(f36,plain,(
% 1.41/0.56    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f61,plain,(
% 1.41/0.56    spl9_1 | ~spl9_2),
% 1.41/0.56    inference(avatar_split_clause,[],[f37,f58,f55])).
% 1.41/0.56  fof(f37,plain,(
% 1.41/0.56    ( ! [X4] : (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (12872)------------------------------
% 1.41/0.56  % (12872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (12872)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (12872)Memory used [KB]: 10874
% 1.41/0.56  % (12872)Time elapsed: 0.140 s
% 1.41/0.56  % (12872)------------------------------
% 1.41/0.56  % (12872)------------------------------
% 1.41/0.56  % (12891)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (12894)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.56  % (12862)Success in time 0.194 s
%------------------------------------------------------------------------------
