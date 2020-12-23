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
% DateTime   : Thu Dec  3 12:57:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 202 expanded)
%              Number of leaves         :   24 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 (1008 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f322,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f68,f80,f131,f249,f255,f289,f300,f304,f310,f313,f321])).

fof(f321,plain,
    ( ~ spl9_18
    | spl9_17 ),
    inference(avatar_split_clause,[],[f319,f298,f302])).

fof(f302,plain,
    ( spl9_18
  <=> r2_hidden(sK8(sK3,sK1,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f298,plain,
    ( spl9_17
  <=> m1_subset_1(sK8(sK3,sK1,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f319,plain,
    ( ~ r2_hidden(sK8(sK3,sK1,sK4),sK2)
    | spl9_17 ),
    inference(resolution,[],[f299,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f299,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f298])).

fof(f313,plain,
    ( ~ spl9_7
    | spl9_19 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl9_7
    | spl9_19 ),
    inference(subsumption_resolution,[],[f79,f311])).

fof(f311,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl9_19 ),
    inference(resolution,[],[f309,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f309,plain,
    ( ~ v1_relat_1(sK3)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl9_19
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl9_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f310,plain,
    ( ~ spl9_19
    | ~ spl9_10
    | spl9_16 ),
    inference(avatar_split_clause,[],[f305,f295,f129,f308])).

fof(f129,plain,
    ( spl9_10
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f295,plain,
    ( spl9_16
  <=> r2_hidden(sK8(sK3,sK1,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f305,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | spl9_16 ),
    inference(resolution,[],[f296,f51])).

fof(f51,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f296,plain,
    ( ~ r2_hidden(sK8(sK3,sK1,sK4),sK1)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f295])).

fof(f304,plain,
    ( spl9_18
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f292,f287,f78,f302])).

fof(f287,plain,
    ( spl9_15
  <=> r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f292,plain,
    ( r2_hidden(sK8(sK3,sK1,sK4),sK2)
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(resolution,[],[f288,f207])).

fof(f207,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(k4_tarski(X5,X6),sK3)
        | r2_hidden(X6,sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f89,f79])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
      | ~ r2_hidden(k4_tarski(X2,X0),X3)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f288,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f287])).

fof(f300,plain,
    ( ~ spl9_16
    | ~ spl9_17
    | ~ spl9_2
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f290,f287,f57,f298,f295])).

fof(f57,plain,
    ( spl9_2
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f290,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK8(sK3,sK1,sK4),sK1)
    | ~ spl9_2
    | ~ spl9_15 ),
    inference(resolution,[],[f288,f58])).

fof(f58,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f289,plain,
    ( spl9_15
    | ~ spl9_7
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f284,f129,f78,f287])).

fof(f284,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3)
    | ~ spl9_7
    | ~ spl9_10 ),
    inference(resolution,[],[f275,f248])).

fof(f248,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f275,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k10_relat_1(sK3,X6))
        | r2_hidden(k4_tarski(X5,sK8(sK3,X6,X5)),sK3) )
    | ~ spl9_7 ),
    inference(resolution,[],[f153,f79])).

fof(f153,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | r2_hidden(k4_tarski(X0,sK8(X1,X2,X0)),X1)
      | ~ r2_hidden(X0,k10_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f52,f45])).

fof(f52,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f255,plain,
    ( spl9_10
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f254,f78,f54,f129])).

fof(f54,plain,
    ( spl9_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f254,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f60,f98])).

fof(f98,plain,
    ( ! [X4] : k8_relset_1(sK0,sK2,sK3,X4) = k10_relat_1(sK3,X4)
    | ~ spl9_7 ),
    inference(resolution,[],[f46,f79])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f60,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f249,plain,
    ( spl9_10
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f245,f78,f66,f62,f129])).

fof(f62,plain,
    ( spl9_3
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f66,plain,
    ( spl9_4
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f245,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f243,f63])).

fof(f63,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f242,f67])).

fof(f67,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f242,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(k4_tarski(X6,X7),sK3)
        | r2_hidden(X6,k10_relat_1(sK3,X8))
        | ~ r2_hidden(X7,X8) )
    | ~ spl9_7 ),
    inference(resolution,[],[f139,f79])).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ r2_hidden(k4_tarski(X2,X0),X3)
      | r2_hidden(X2,k10_relat_1(X3,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f50,f45])).

fof(f50,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f131,plain,
    ( ~ spl9_10
    | spl9_1
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f127,f78,f54,f129])).

fof(f127,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl9_1
    | ~ spl9_7 ),
    inference(superposition,[],[f55,f98])).

fof(f55,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f80,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK4,sK5),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X4,X5),X3)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X4,X6),X3)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X4,X5),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X4,X6),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X4,X5),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X4,X6),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(sK4,X6),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(sK4,X6),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK4,sK5),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X4,X6),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f68,plain,
    ( spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f34,f66,f54])).

fof(f34,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f35,f62,f54])).

fof(f35,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f36,f57,f54])).

fof(f36,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.41  % (9103)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.42  % (9111)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.43  % (9103)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f322,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f59,f64,f68,f80,f131,f249,f255,f289,f300,f304,f310,f313,f321])).
% 0.19/0.44  fof(f321,plain,(
% 0.19/0.44    ~spl9_18 | spl9_17),
% 0.19/0.44    inference(avatar_split_clause,[],[f319,f298,f302])).
% 0.19/0.44  fof(f302,plain,(
% 0.19/0.44    spl9_18 <=> r2_hidden(sK8(sK3,sK1,sK4),sK2)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.19/0.44  fof(f298,plain,(
% 0.19/0.44    spl9_17 <=> m1_subset_1(sK8(sK3,sK1,sK4),sK2)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.19/0.44  fof(f319,plain,(
% 0.19/0.44    ~r2_hidden(sK8(sK3,sK1,sK4),sK2) | spl9_17),
% 0.19/0.44    inference(resolution,[],[f299,f43])).
% 0.19/0.44  fof(f43,plain,(
% 0.19/0.44    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.44  fof(f299,plain,(
% 0.19/0.44    ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | spl9_17),
% 0.19/0.44    inference(avatar_component_clause,[],[f298])).
% 0.19/0.44  fof(f313,plain,(
% 0.19/0.44    ~spl9_7 | spl9_19),
% 0.19/0.44    inference(avatar_contradiction_clause,[],[f312])).
% 0.19/0.44  fof(f312,plain,(
% 0.19/0.44    $false | (~spl9_7 | spl9_19)),
% 0.19/0.44    inference(subsumption_resolution,[],[f79,f311])).
% 0.19/0.44  fof(f311,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl9_19),
% 0.19/0.44    inference(resolution,[],[f309,f45])).
% 0.19/0.44  fof(f45,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.44  fof(f309,plain,(
% 0.19/0.44    ~v1_relat_1(sK3) | spl9_19),
% 0.19/0.44    inference(avatar_component_clause,[],[f308])).
% 0.19/0.44  fof(f308,plain,(
% 0.19/0.44    spl9_19 <=> v1_relat_1(sK3)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.19/0.44  fof(f79,plain,(
% 0.19/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl9_7),
% 0.19/0.44    inference(avatar_component_clause,[],[f78])).
% 0.19/0.44  fof(f78,plain,(
% 0.19/0.44    spl9_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.19/0.44  fof(f310,plain,(
% 0.19/0.44    ~spl9_19 | ~spl9_10 | spl9_16),
% 0.19/0.44    inference(avatar_split_clause,[],[f305,f295,f129,f308])).
% 0.19/0.44  fof(f129,plain,(
% 0.19/0.44    spl9_10 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.19/0.44  fof(f295,plain,(
% 0.19/0.44    spl9_16 <=> r2_hidden(sK8(sK3,sK1,sK4),sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.19/0.44  fof(f305,plain,(
% 0.19/0.44    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | spl9_16),
% 0.19/0.44    inference(resolution,[],[f296,f51])).
% 0.19/0.44  fof(f51,plain,(
% 0.19/0.44    ( ! [X6,X0,X1] : (r2_hidden(sK8(X0,X1,X6),X1) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(equality_resolution,[],[f38])).
% 0.19/0.44  fof(f38,plain,(
% 0.19/0.44    ( ! [X6,X2,X0,X1] : (r2_hidden(sK8(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f28])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f24,f27,f26,f25])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(rectify,[],[f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(nnf_transformation,[],[f11])).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.19/0.44  fof(f296,plain,(
% 0.19/0.44    ~r2_hidden(sK8(sK3,sK1,sK4),sK1) | spl9_16),
% 0.19/0.44    inference(avatar_component_clause,[],[f295])).
% 0.19/0.44  fof(f304,plain,(
% 0.19/0.44    spl9_18 | ~spl9_7 | ~spl9_15),
% 0.19/0.44    inference(avatar_split_clause,[],[f292,f287,f78,f302])).
% 0.19/0.44  fof(f287,plain,(
% 0.19/0.44    spl9_15 <=> r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.19/0.44  fof(f292,plain,(
% 0.19/0.44    r2_hidden(sK8(sK3,sK1,sK4),sK2) | (~spl9_7 | ~spl9_15)),
% 0.19/0.44    inference(resolution,[],[f288,f207])).
% 0.19/0.44  fof(f207,plain,(
% 0.19/0.44    ( ! [X6,X5] : (~r2_hidden(k4_tarski(X5,X6),sK3) | r2_hidden(X6,sK2)) ) | ~spl9_7),
% 0.19/0.44    inference(resolution,[],[f89,f79])).
% 0.19/0.44  fof(f89,plain,(
% 0.19/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) | ~r2_hidden(k4_tarski(X2,X0),X3) | r2_hidden(X0,X1)) )),
% 0.19/0.44    inference(resolution,[],[f48,f44])).
% 0.19/0.44  fof(f44,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.19/0.44  fof(f48,plain,(
% 0.19/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f30])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.44    inference(flattening,[],[f29])).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.44    inference(nnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.19/0.44  fof(f288,plain,(
% 0.19/0.44    r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3) | ~spl9_15),
% 0.19/0.44    inference(avatar_component_clause,[],[f287])).
% 0.19/0.44  fof(f300,plain,(
% 0.19/0.44    ~spl9_16 | ~spl9_17 | ~spl9_2 | ~spl9_15),
% 0.19/0.44    inference(avatar_split_clause,[],[f290,f287,f57,f298,f295])).
% 0.19/0.44  fof(f57,plain,(
% 0.19/0.44    spl9_2 <=> ! [X5] : (~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.19/0.44  fof(f290,plain,(
% 0.19/0.44    ~m1_subset_1(sK8(sK3,sK1,sK4),sK2) | ~r2_hidden(sK8(sK3,sK1,sK4),sK1) | (~spl9_2 | ~spl9_15)),
% 0.19/0.44    inference(resolution,[],[f288,f58])).
% 0.19/0.44  fof(f58,plain,(
% 0.19/0.44    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1)) ) | ~spl9_2),
% 0.19/0.44    inference(avatar_component_clause,[],[f57])).
% 0.19/0.44  fof(f289,plain,(
% 0.19/0.44    spl9_15 | ~spl9_7 | ~spl9_10),
% 0.19/0.44    inference(avatar_split_clause,[],[f284,f129,f78,f287])).
% 0.19/0.44  fof(f284,plain,(
% 0.19/0.44    r2_hidden(k4_tarski(sK4,sK8(sK3,sK1,sK4)),sK3) | (~spl9_7 | ~spl9_10)),
% 0.19/0.44    inference(resolution,[],[f275,f248])).
% 0.19/0.44  fof(f248,plain,(
% 0.19/0.44    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl9_10),
% 0.19/0.44    inference(avatar_component_clause,[],[f129])).
% 0.19/0.44  fof(f275,plain,(
% 0.19/0.44    ( ! [X6,X5] : (~r2_hidden(X5,k10_relat_1(sK3,X6)) | r2_hidden(k4_tarski(X5,sK8(sK3,X6,X5)),sK3)) ) | ~spl9_7),
% 0.19/0.44    inference(resolution,[],[f153,f79])).
% 0.19/0.44  fof(f153,plain,(
% 0.19/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | r2_hidden(k4_tarski(X0,sK8(X1,X2,X0)),X1) | ~r2_hidden(X0,k10_relat_1(X1,X2))) )),
% 0.19/0.44    inference(resolution,[],[f52,f45])).
% 0.19/0.44  fof(f52,plain,(
% 0.19/0.44    ( ! [X6,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)) )),
% 0.19/0.44    inference(equality_resolution,[],[f37])).
% 0.19/0.44  fof(f37,plain,(
% 0.19/0.44    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f28])).
% 0.19/0.44  fof(f255,plain,(
% 0.19/0.44    spl9_10 | ~spl9_1 | ~spl9_7),
% 0.19/0.44    inference(avatar_split_clause,[],[f254,f78,f54,f129])).
% 0.19/0.44  fof(f54,plain,(
% 0.19/0.44    spl9_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.19/0.44  fof(f254,plain,(
% 0.19/0.44    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl9_1 | ~spl9_7)),
% 0.19/0.44    inference(forward_demodulation,[],[f60,f98])).
% 0.19/0.44  fof(f98,plain,(
% 0.19/0.44    ( ! [X4] : (k8_relset_1(sK0,sK2,sK3,X4) = k10_relat_1(sK3,X4)) ) | ~spl9_7),
% 0.19/0.44    inference(resolution,[],[f46,f79])).
% 0.19/0.44  fof(f46,plain,(
% 0.19/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,axiom,(
% 0.19/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.19/0.44  fof(f60,plain,(
% 0.19/0.44    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl9_1),
% 0.19/0.44    inference(avatar_component_clause,[],[f54])).
% 0.19/0.44  fof(f249,plain,(
% 0.19/0.44    spl9_10 | ~spl9_3 | ~spl9_4 | ~spl9_7),
% 0.19/0.44    inference(avatar_split_clause,[],[f245,f78,f66,f62,f129])).
% 0.19/0.44  fof(f62,plain,(
% 0.19/0.44    spl9_3 <=> r2_hidden(sK5,sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.19/0.44  fof(f66,plain,(
% 0.19/0.44    spl9_4 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.19/0.44  fof(f245,plain,(
% 0.19/0.44    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl9_3 | ~spl9_4 | ~spl9_7)),
% 0.19/0.44    inference(resolution,[],[f243,f63])).
% 0.19/0.44  fof(f63,plain,(
% 0.19/0.44    r2_hidden(sK5,sK1) | ~spl9_3),
% 0.19/0.44    inference(avatar_component_clause,[],[f62])).
% 0.19/0.44  fof(f243,plain,(
% 0.19/0.44    ( ! [X0] : (~r2_hidden(sK5,X0) | r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | (~spl9_4 | ~spl9_7)),
% 0.19/0.44    inference(resolution,[],[f242,f67])).
% 0.19/0.44  fof(f67,plain,(
% 0.19/0.44    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl9_4),
% 0.19/0.44    inference(avatar_component_clause,[],[f66])).
% 0.19/0.44  fof(f242,plain,(
% 0.19/0.44    ( ! [X6,X8,X7] : (~r2_hidden(k4_tarski(X6,X7),sK3) | r2_hidden(X6,k10_relat_1(sK3,X8)) | ~r2_hidden(X7,X8)) ) | ~spl9_7),
% 0.19/0.44    inference(resolution,[],[f139,f79])).
% 0.19/0.44  fof(f139,plain,(
% 0.19/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~r2_hidden(k4_tarski(X2,X0),X3) | r2_hidden(X2,k10_relat_1(X3,X1)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.44    inference(resolution,[],[f50,f45])).
% 0.19/0.44  fof(f50,plain,(
% 0.19/0.44    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | r2_hidden(X6,k10_relat_1(X0,X1))) )),
% 0.19/0.44    inference(equality_resolution,[],[f39])).
% 0.19/0.44  fof(f39,plain,(
% 0.19/0.44    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f28])).
% 0.19/0.44  fof(f131,plain,(
% 0.19/0.44    ~spl9_10 | spl9_1 | ~spl9_7),
% 0.19/0.44    inference(avatar_split_clause,[],[f127,f78,f54,f129])).
% 0.19/0.44  fof(f127,plain,(
% 0.19/0.44    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (spl9_1 | ~spl9_7)),
% 0.19/0.44    inference(superposition,[],[f55,f98])).
% 0.19/0.44  fof(f55,plain,(
% 0.19/0.44    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl9_1),
% 0.19/0.44    inference(avatar_component_clause,[],[f54])).
% 0.19/0.44  fof(f80,plain,(
% 0.19/0.44    spl9_7),
% 0.19/0.44    inference(avatar_split_clause,[],[f31,f78])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.19/0.44    inference(cnf_transformation,[],[f22])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & ((r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(sK4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(X4,sK0)) => ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(sK4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(sK4,sK0))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(sK4,X6),sK3) & m1_subset_1(X6,sK2)) => (r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.44    inference(rectify,[],[f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.44    inference(flattening,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.44    inference(nnf_transformation,[],[f10])).
% 0.19/0.44  fof(f10,plain,(
% 0.19/0.44    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.44    inference(ennf_transformation,[],[f9])).
% 0.19/0.44  fof(f9,plain,(
% 0.19/0.44    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.19/0.44    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.44  fof(f8,negated_conjecture,(
% 0.19/0.44    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.19/0.44    inference(negated_conjecture,[],[f7])).
% 0.19/0.44  fof(f7,conjecture,(
% 0.19/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.19/0.44  fof(f68,plain,(
% 0.19/0.44    spl9_1 | spl9_4),
% 0.19/0.44    inference(avatar_split_clause,[],[f34,f66,f54])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.19/0.44    inference(cnf_transformation,[],[f22])).
% 0.19/0.44  fof(f64,plain,(
% 0.19/0.44    spl9_1 | spl9_3),
% 0.19/0.44    inference(avatar_split_clause,[],[f35,f62,f54])).
% 0.19/0.44  fof(f35,plain,(
% 0.19/0.44    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.19/0.44    inference(cnf_transformation,[],[f22])).
% 0.19/0.44  fof(f59,plain,(
% 0.19/0.44    ~spl9_1 | spl9_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f36,f57,f54])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    ( ! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f22])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (9103)------------------------------
% 0.19/0.44  % (9103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (9103)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (9103)Memory used [KB]: 10874
% 0.19/0.44  % (9103)Time elapsed: 0.045 s
% 0.19/0.44  % (9103)------------------------------
% 0.19/0.44  % (9103)------------------------------
% 0.19/0.45  % (9096)Success in time 0.095 s
%------------------------------------------------------------------------------
