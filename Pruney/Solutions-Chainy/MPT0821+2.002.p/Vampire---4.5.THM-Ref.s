%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 269 expanded)
%              Number of leaves         :   25 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  350 (1090 expanded)
%              Number of equality atoms :   52 ( 217 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f78,f93,f96,f127,f129,f139,f148,f153,f154,f158])).

fof(f158,plain,
    ( ~ spl9_2
    | spl9_8 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl9_2
    | spl9_8 ),
    inference(subsumption_resolution,[],[f156,f108])).

fof(f108,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl9_8
  <=> sK1 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f156,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f122,f67])).

fof(f67,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl9_2
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f122,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | ! [X5] :
          ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( sK1 != k1_relset_1(sK1,sK0,sK2)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK2)
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k1_relset_1(sK1,sK0,sK2)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK2)
            | ~ r2_hidden(X5,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK2)
        & r2_hidden(X3,sK1) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK2)
     => r2_hidden(k4_tarski(X5,sK4(X5)),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f154,plain,
    ( ~ spl9_9
    | spl9_8
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f152,f91,f107,f112])).

fof(f112,plain,
    ( spl9_9
  <=> r1_tarski(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f91,plain,
    ( spl9_6
  <=> ! [X0] :
        ( r1_tarski(k1_relat_1(sK2),X0)
        | ~ v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f152,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl9_6 ),
    inference(resolution,[],[f99,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f99,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl9_6 ),
    inference(resolution,[],[f98,f38])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f92,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f92,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f153,plain,
    ( ~ spl9_7
    | spl9_8
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f151,f91,f107,f103])).

fof(f103,plain,
    ( spl9_7
  <=> r2_hidden(sK5(sK1,k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f151,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ r2_hidden(sK5(sK1,k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl9_6 ),
    inference(resolution,[],[f99,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ r2_hidden(sK5(X1,X0),X0) ) ),
    inference(resolution,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f148,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f146,f73])).

fof(f73,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl9_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f146,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f142,f109])).

fof(f109,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f142,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f64,f61])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f33,f36,f35,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f64,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f139,plain,
    ( ~ spl9_6
    | ~ spl9_8
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_8
    | spl9_9 ),
    inference(subsumption_resolution,[],[f133,f132])).

fof(f132,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(backward_demodulation,[],[f99,f109])).

fof(f133,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl9_8
    | spl9_9 ),
    inference(backward_demodulation,[],[f114,f109])).

fof(f114,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f129,plain,
    ( spl9_2
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl9_2
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f109,f123])).

fof(f123,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl9_2 ),
    inference(superposition,[],[f68,f122])).

fof(f68,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f127,plain,
    ( ~ spl9_4
    | spl9_7
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl9_4
    | spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f124,f114])).

fof(f124,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl9_4
    | spl9_7 ),
    inference(resolution,[],[f119,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f119,plain,
    ( ~ r2_hidden(sK5(sK1,k1_relat_1(sK2)),sK1)
    | ~ spl9_4
    | spl9_7 ),
    inference(resolution,[],[f117,f77])).

fof(f77,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl9_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f117,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK1,k1_relat_1(sK2)),X0),sK2)
    | spl9_7 ),
    inference(resolution,[],[f105,f60])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f105,plain,
    ( ~ r2_hidden(sK5(sK1,k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl9_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f96,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl9_5 ),
    inference(resolution,[],[f94,f38])).

fof(f94,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl9_5 ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl9_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f93,plain,
    ( ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f85,f91,f87])).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK2),X0)
      | ~ v4_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f82,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f82,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(resolution,[],[f79,f38])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relat_1(k7_relat_1(X0,X3)),X3) ) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f78,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f39,f66,f76])).

fof(f39,plain,(
    ! [X5] :
      ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f40,f66,f71])).

fof(f40,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f41,f66,f63])).

fof(f41,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.32  % Computer   : n018.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 09:41:26 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.20/0.49  % (5234)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (5234)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (5238)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (5253)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (5245)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (5258)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (5246)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f69,f74,f78,f93,f96,f127,f129,f139,f148,f153,f154,f158])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    ~spl9_2 | spl9_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f157])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    $false | (~spl9_2 | spl9_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f156,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    sK1 != k1_relat_1(sK2) | spl9_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl9_8 <=> sK1 = k1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    sK1 = k1_relat_1(sK2) | ~spl9_2),
% 0.20/0.53    inference(forward_demodulation,[],[f122,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    sK1 = k1_relset_1(sK1,sK0,sK2) | ~spl9_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl9_2 <=> sK1 = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f55,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    (sK1 != k1_relset_1(sK1,sK0,sK2) | (! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2) & r2_hidden(sK3,sK1))) & (sK1 = k1_relset_1(sK1,sK0,sK2) | ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f24,f23,f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((sK1 != k1_relset_1(sK1,sK0,sK2) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK2) & r2_hidden(X3,sK1))) & (sK1 = k1_relset_1(sK1,sK0,sK2) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK2) & r2_hidden(X3,sK1)) => (! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2) & r2_hidden(sK3,sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK2) => r2_hidden(k4_tarski(X5,sK4(X5)),sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.53    inference(rectify,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.53    inference(nnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.53    inference(negated_conjecture,[],[f9])).
% 0.20/0.53  fof(f9,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    ~spl9_9 | spl9_8 | ~spl9_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f152,f91,f107,f112])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    spl9_9 <=> r1_tarski(sK1,k1_relat_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl9_6 <=> ! [X0] : (r1_tarski(k1_relat_1(sK2),X0) | ~v4_relat_1(sK2,X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    sK1 = k1_relat_1(sK2) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~spl9_6),
% 0.20/0.53    inference(resolution,[],[f99,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK2),sK1) | ~spl9_6),
% 0.20/0.53    inference(resolution,[],[f98,f38])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl9_6),
% 0.20/0.53    inference(resolution,[],[f92,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X0] : (~v4_relat_1(sK2,X0) | r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl9_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f91])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    ~spl9_7 | spl9_8 | ~spl9_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f151,f91,f107,f103])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    spl9_7 <=> r2_hidden(sK5(sK1,k1_relat_1(sK2)),k1_relat_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    sK1 = k1_relat_1(sK2) | ~r2_hidden(sK5(sK1,k1_relat_1(sK2)),k1_relat_1(sK2)) | ~spl9_6),
% 0.20/0.53    inference(resolution,[],[f99,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~r2_hidden(sK5(X1,X0),X0)) )),
% 0.20/0.53    inference(resolution,[],[f46,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    ~spl9_1 | ~spl9_3 | ~spl9_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f147])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    $false | (~spl9_1 | ~spl9_3 | ~spl9_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f146,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    r2_hidden(sK3,sK1) | ~spl9_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl9_3 <=> r2_hidden(sK3,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    ~r2_hidden(sK3,sK1) | (~spl9_1 | ~spl9_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f142,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    sK1 = k1_relat_1(sK2) | ~spl9_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f107])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~spl9_1),
% 0.20/0.53    inference(resolution,[],[f64,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.53    inference(equality_resolution,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f33,f36,f35,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.53    inference(rectify,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2)) ) | ~spl9_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    spl9_1 <=> ! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ~spl9_6 | ~spl9_8 | spl9_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    $false | (~spl9_6 | ~spl9_8 | spl9_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f133,f132])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    r1_tarski(sK1,sK1) | (~spl9_6 | ~spl9_8)),
% 0.20/0.53    inference(backward_demodulation,[],[f99,f109])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK1) | (~spl9_8 | spl9_9)),
% 0.20/0.53    inference(backward_demodulation,[],[f114,f109])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl9_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f112])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    spl9_2 | ~spl9_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    $false | (spl9_2 | ~spl9_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f109,f123])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    sK1 != k1_relat_1(sK2) | spl9_2),
% 0.20/0.53    inference(superposition,[],[f68,f122])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    sK1 != k1_relset_1(sK1,sK0,sK2) | spl9_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f66])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ~spl9_4 | spl9_7 | spl9_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    $false | (~spl9_4 | spl9_7 | spl9_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f124,f114])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    r1_tarski(sK1,k1_relat_1(sK2)) | (~spl9_4 | spl9_7)),
% 0.20/0.53    inference(resolution,[],[f119,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ~r2_hidden(sK5(sK1,k1_relat_1(sK2)),sK1) | (~spl9_4 | spl9_7)),
% 0.20/0.53    inference(resolution,[],[f117,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1)) ) | ~spl9_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl9_4 <=> ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK1,k1_relat_1(sK2)),X0),sK2)) ) | spl9_7),
% 0.20/0.53    inference(resolution,[],[f105,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ~r2_hidden(sK5(sK1,k1_relat_1(sK2)),k1_relat_1(sK2)) | spl9_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f103])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    spl9_5),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f95])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    $false | spl9_5),
% 0.20/0.54    inference(resolution,[],[f94,f38])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl9_5),
% 0.20/0.54    inference(resolution,[],[f89,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | spl9_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    spl9_5 <=> v1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ~spl9_5 | spl9_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f85,f91,f87])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.54    inference(superposition,[],[f82,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 0.20/0.54    inference(resolution,[],[f79,f38])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relat_1(k7_relat_1(X0,X3)),X3)) )),
% 0.20/0.54    inference(resolution,[],[f54,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    spl9_4 | spl9_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f39,f66,f76])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X5] : (sK1 = k1_relset_1(sK1,sK0,sK2) | r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    spl9_3 | ~spl9_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f40,f66,f71])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    sK1 != k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    spl9_1 | ~spl9_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f41,f66,f63])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X4] : (sK1 != k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (5234)------------------------------
% 0.20/0.54  % (5234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5234)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (5234)Memory used [KB]: 10746
% 0.20/0.54  % (5234)Time elapsed: 0.133 s
% 0.20/0.54  % (5234)------------------------------
% 0.20/0.54  % (5234)------------------------------
% 0.20/0.54  % (5254)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (5230)Success in time 0.2 s
%------------------------------------------------------------------------------
