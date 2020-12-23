%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 186 expanded)
%              Number of leaves         :   22 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  270 ( 755 expanded)
%              Number of equality atoms :   51 ( 147 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17800)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (17796)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f52,f56,f61,f66,f72,f91,f93,f99,f105,f106,f121])).

fof(f121,plain,
    ( ~ spl8_3
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f120,f64,f38,f45])).

fof(f45,plain,
    ( spl8_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f38,plain,
    ( spl8_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f64,plain,
    ( spl8_7
  <=> sK1 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f120,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f116,f87])).

fof(f87,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f116,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_1 ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f39,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f106,plain,
    ( spl8_9
    | spl8_7
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f94,f89,f64,f85])).

fof(f85,plain,
    ( spl8_9
  <=> r2_hidden(sK5(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f89,plain,
    ( spl8_10
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f94,plain,
    ( sK1 = k1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK1),sK1)
    | ~ spl8_10 ),
    inference(resolution,[],[f90,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f105,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | sK1 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f99,plain,
    ( ~ spl8_9
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f95,f89,f49,f85])).

fof(f49,plain,
    ( spl8_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f95,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f93,plain,
    ( spl8_7
    | spl8_10
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f92,f85,f89,f64])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2)
        | sK1 = k1_relat_1(sK2) )
    | ~ spl8_9 ),
    inference(resolution,[],[f86,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f91,plain,
    ( spl8_9
    | spl8_7
    | spl8_10
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f83,f70,f89,f64,f85])).

fof(f70,plain,
    ( spl8_8
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2)
        | sK1 = k1_relat_1(sK2)
        | r2_hidden(sK5(sK2,sK1),sK1) )
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2)
        | sK1 = k1_relat_1(sK2)
        | sK1 = k1_relat_1(sK2)
        | r2_hidden(sK5(sK2,sK1),sK1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f77,f31])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK5(X0,sK1),X2),sK2)
        | ~ r2_hidden(k4_tarski(sK5(X0,sK1),X1),X0)
        | k1_relat_1(X0) = sK1 )
    | ~ spl8_8 ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK5(X2,sK1),k1_relat_1(sK2))
        | k1_relat_1(X2) = sK1
        | ~ r2_hidden(k4_tarski(sK5(X2,sK1),X3),X2) )
    | ~ spl8_8 ),
    inference(resolution,[],[f74,f71])).

fof(f71,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f74,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X5))
      | k1_relat_1(X4) = X5
      | ~ r2_hidden(sK5(X4,X5),X7)
      | ~ r2_hidden(k4_tarski(sK5(X4,X5),X6),X4) ) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f72,plain,
    ( spl8_8
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f68,f59,f54,f70])).

fof(f54,plain,
    ( spl8_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f59,plain,
    ( spl8_6
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f68,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f67,f60])).

fof(f60,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f67,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl8_5 ),
    inference(resolution,[],[f34,f55])).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f66,plain,
    ( ~ spl8_7
    | spl8_2
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f62,f59,f41,f64])).

fof(f41,plain,
    ( spl8_2
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f62,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl8_2
    | ~ spl8_6 ),
    inference(superposition,[],[f42,f60])).

fof(f42,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f61,plain,
    ( spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f57,f54,f59])).

fof(f57,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f33,f55])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f56,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | ! [X5] :
          ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f16,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK2)
        & r2_hidden(X3,sK1) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK2)
     => r2_hidden(k4_tarski(X5,sK4(X5)),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f52,plain,
    ( spl8_4
    | spl8_2 ),
    inference(avatar_split_clause,[],[f25,f41,f49])).

fof(f25,plain,(
    ! [X5] :
      ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f26,f41,f45])).

fof(f26,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

% (17802)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f43,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f27,f41,f38])).

fof(f27,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (17788)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (17795)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (17803)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (17794)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (17786)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (17797)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (17801)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (17785)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (17784)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (17789)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (17783)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (17789)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (17800)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (17796)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f43,f47,f52,f56,f61,f66,f72,f91,f93,f99,f105,f106,f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ~spl8_3 | ~spl8_1 | ~spl8_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f120,f64,f38,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl8_3 <=> r2_hidden(sK3,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    spl8_1 <=> ! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl8_7 <=> sK1 = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ~r2_hidden(sK3,sK1) | (~spl8_1 | ~spl8_7)),
% 0.20/0.51    inference(forward_demodulation,[],[f116,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK2) | ~spl8_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~spl8_1),
% 0.20/0.51    inference(resolution,[],[f39,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.51    inference(equality_resolution,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f22,f21,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.51    inference(rectify,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2)) ) | ~spl8_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f38])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl8_9 | spl8_7 | ~spl8_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f94,f89,f64,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl8_9 <=> r2_hidden(sK5(sK2,sK1),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl8_10 <=> ! [X0] : ~r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK2) | r2_hidden(sK5(sK2,sK1),sK1) | ~spl8_10),
% 0.20/0.51    inference(resolution,[],[f90,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2)) ) | ~spl8_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    sK1 != k1_relset_1(sK1,sK0,sK2) | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | sK1 = k1_relat_1(sK2)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ~spl8_9 | ~spl8_4 | ~spl8_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f95,f89,f49,f85])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    spl8_4 <=> ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ~r2_hidden(sK5(sK2,sK1),sK1) | (~spl8_4 | ~spl8_10)),
% 0.20/0.51    inference(resolution,[],[f90,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1)) ) | ~spl8_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f49])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl8_7 | spl8_10 | ~spl8_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f92,f85,f89,f64])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2) | sK1 = k1_relat_1(sK2)) ) | ~spl8_9),
% 0.20/0.51    inference(resolution,[],[f86,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | k1_relat_1(X0) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    r2_hidden(sK5(sK2,sK1),sK1) | ~spl8_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl8_9 | spl8_7 | spl8_10 | ~spl8_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f83,f70,f89,f64,f85])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl8_8 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2) | sK1 = k1_relat_1(sK2) | r2_hidden(sK5(sK2,sK1),sK1)) ) | ~spl8_8),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK2,sK1),X0),sK2) | sK1 = k1_relat_1(sK2) | sK1 = k1_relat_1(sK2) | r2_hidden(sK5(sK2,sK1),sK1)) ) | ~spl8_8),
% 0.20/0.51    inference(resolution,[],[f77,f31])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(sK5(X0,sK1),X2),sK2) | ~r2_hidden(k4_tarski(sK5(X0,sK1),X1),X0) | k1_relat_1(X0) = sK1) ) | ~spl8_8),
% 0.20/0.51    inference(resolution,[],[f76,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r2_hidden(sK5(X2,sK1),k1_relat_1(sK2)) | k1_relat_1(X2) = sK1 | ~r2_hidden(k4_tarski(sK5(X2,sK1),X3),X2)) ) | ~spl8_8),
% 0.20/0.51    inference(resolution,[],[f74,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl8_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(X5)) | k1_relat_1(X4) = X5 | ~r2_hidden(sK5(X4,X5),X7) | ~r2_hidden(k4_tarski(sK5(X4,X5),X6),X4)) )),
% 0.20/0.51    inference(resolution,[],[f32,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl8_8 | ~spl8_5 | ~spl8_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f68,f59,f54,f70])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl8_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl8_6 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl8_5 | ~spl8_6)),
% 0.20/0.51    inference(forward_demodulation,[],[f67,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl8_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | ~spl8_5),
% 0.20/0.51    inference(resolution,[],[f34,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl8_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ~spl8_7 | spl8_2 | ~spl8_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f62,f59,f41,f64])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    spl8_2 <=> sK1 = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    sK1 != k1_relat_1(sK2) | (spl8_2 | ~spl8_6)),
% 0.20/0.51    inference(superposition,[],[f42,f60])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    sK1 != k1_relset_1(sK1,sK0,sK2) | spl8_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f41])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl8_6 | ~spl8_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f57,f54,f59])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl8_5),
% 0.20/0.51    inference(resolution,[],[f33,f55])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    spl8_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f54])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    (sK1 != k1_relset_1(sK1,sK0,sK2) | (! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2) & r2_hidden(sK3,sK1))) & (sK1 = k1_relset_1(sK1,sK0,sK2) | ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f16,f15,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((sK1 != k1_relset_1(sK1,sK0,sK2) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK2) & r2_hidden(X3,sK1))) & (sK1 = k1_relset_1(sK1,sK0,sK2) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK2) & r2_hidden(X3,sK1)) => (! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2) & r2_hidden(sK3,sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK2) => r2_hidden(k4_tarski(X5,sK4(X5)),sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.51    inference(rectify,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.51    inference(nnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    spl8_4 | spl8_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f41,f49])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X5] : (sK1 = k1_relset_1(sK1,sK0,sK2) | r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    spl8_3 | ~spl8_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f41,f45])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    sK1 != k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  % (17802)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    spl8_1 | ~spl8_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f41,f38])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X4] : (sK1 != k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (17789)------------------------------
% 0.20/0.51  % (17789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17789)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (17789)Memory used [KB]: 10746
% 0.20/0.51  % (17789)Time elapsed: 0.007 s
% 0.20/0.51  % (17789)------------------------------
% 0.20/0.51  % (17789)------------------------------
% 0.20/0.52  % (17794)Refutation not found, incomplete strategy% (17794)------------------------------
% 0.20/0.52  % (17794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17794)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17794)Memory used [KB]: 10618
% 0.20/0.52  % (17794)Time elapsed: 0.101 s
% 0.20/0.52  % (17794)------------------------------
% 0.20/0.52  % (17794)------------------------------
% 0.20/0.52  % (17782)Success in time 0.163 s
%------------------------------------------------------------------------------
