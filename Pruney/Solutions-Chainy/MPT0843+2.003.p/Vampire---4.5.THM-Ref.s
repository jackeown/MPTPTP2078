%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 193 expanded)
%              Number of leaves         :   25 (  89 expanded)
%              Depth                    :    9
%              Number of atoms          :  340 ( 736 expanded)
%              Number of equality atoms :   14 (  41 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f669,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f70,f75,f97,f113,f127,f144,f205,f206,f207,f393,f399,f665,f667,f668])).

fof(f668,plain,
    ( k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) != k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))
    | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | ~ r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f667,plain,
    ( k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) != k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))
    | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)))
    | ~ r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f665,plain,
    ( spl7_74
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f609,f383,f661])).

fof(f661,plain,
    ( spl7_74
  <=> k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f383,plain,
    ( spl7_44
  <=> r2_hidden(sK3(sK0,sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f609,plain,
    ( k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))
    | ~ spl7_44 ),
    inference(resolution,[],[f385,f29])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    & ! [X3] :
        ( k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3)
        | ~ r2_hidden(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & ! [X3] :
                ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,sK1,X2)
          & ! [X3] :
              ( k11_relat_1(X2,X3) = k11_relat_1(sK1,X3)
              | ~ r2_hidden(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,sK1,X2)
        & ! [X3] :
            ( k11_relat_1(X2,X3) = k11_relat_1(sK1,X3)
            | ~ r2_hidden(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
   => ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
      & ! [X3] :
          ( k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3)
          | ~ r2_hidden(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ! [X3] :
                  ( r2_hidden(X3,X0)
                 => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

fof(f385,plain,
    ( r2_hidden(sK3(sK0,sK0,sK1,sK2),sK0)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f383])).

fof(f399,plain,
    ( spl7_10
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f234,f90,f60,f110])).

fof(f110,plain,
    ( spl7_10
  <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f60,plain,
    ( spl7_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f90,plain,
    ( spl7_8
  <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f234,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0))
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f62,f92,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
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

fof(f92,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f393,plain,
    ( spl7_44
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f330,f110,f383])).

fof(f330,plain,
    ( r2_hidden(sK3(sK0,sK0,sK1,sK2),sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f112,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f112,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f207,plain,
    ( ~ spl7_8
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f98,f94,f60,f55,f50,f90])).

fof(f50,plain,
    ( spl7_1
  <=> r2_relset_1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f55,plain,
    ( spl7_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f94,plain,
    ( spl7_9
  <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f98,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f52,f62,f57,f96,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
      | r2_relset_1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
                & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
                & m1_subset_1(sK4(X0,X1,X2,X3),X1)
                & m1_subset_1(sK3(X0,X1,X2,X3),X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f22,f21])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ r2_hidden(k4_tarski(X4,X5),X2) )
              & ( r2_hidden(k4_tarski(X4,X5),X3)
                | r2_hidden(k4_tarski(X4,X5),X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
            & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
              | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK3(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
            | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
            | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
          & m1_subset_1(X5,X1) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
        & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
          | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
        & m1_subset_1(sK4(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).

fof(f96,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f52,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f206,plain,
    ( spl7_9
    | ~ spl7_5
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f164,f121,f72,f94])).

fof(f72,plain,
    ( spl7_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f121,plain,
    ( spl7_12
  <=> r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f164,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | ~ spl7_5
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f74,f123,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f123,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f74,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f205,plain,
    ( ~ spl7_4
    | spl7_14
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f195,f90,f141,f67])).

fof(f67,plain,
    ( spl7_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f141,plain,
    ( spl7_14
  <=> r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f195,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ spl7_8 ),
    inference(resolution,[],[f92,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f144,plain,
    ( ~ spl7_14
    | ~ spl7_4
    | spl7_8 ),
    inference(avatar_split_clause,[],[f131,f90,f67,f141])).

fof(f131,plain,
    ( ~ r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | ~ spl7_4
    | spl7_8 ),
    inference(unit_resulting_resolution,[],[f69,f91,f38])).

fof(f91,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f69,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f127,plain,
    ( ~ spl7_5
    | spl7_12
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f106,f94,f121,f72])).

fof(f106,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(resolution,[],[f96,f37])).

fof(f113,plain,
    ( spl7_10
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f102,f94,f55,f110])).

fof(f102,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0))
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f57,f96,f42])).

fof(f97,plain,
    ( ~ spl7_3
    | ~ spl7_2
    | spl7_8
    | spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f88,f50,f94,f90,f55,f60])).

fof(f88,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_1 ),
    inference(resolution,[],[f35,f52])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f64,f55,f72])).

fof(f64,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f44,f57,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f70,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f65,f60,f67])).

fof(f65,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f44,f62,f43])).

fof(f63,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f30,f50])).

fof(f30,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (8115)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.47  % (8104)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.47  % (8108)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.47  % (8107)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.47  % (8124)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.47  % (8104)Refutation not found, incomplete strategy% (8104)------------------------------
% 0.19/0.47  % (8104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (8104)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (8104)Memory used [KB]: 10618
% 0.19/0.47  % (8104)Time elapsed: 0.059 s
% 0.19/0.47  % (8104)------------------------------
% 0.19/0.47  % (8104)------------------------------
% 0.19/0.48  % (8111)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.48  % (8110)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.48  % (8108)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % (8116)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.49  % (8122)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f669,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f53,f58,f63,f70,f75,f97,f113,f127,f144,f205,f206,f207,f393,f399,f665,f667,f668])).
% 0.19/0.49  fof(f668,plain,(
% 0.19/0.49    k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) != k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | ~r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)))),
% 0.19/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.49  fof(f667,plain,(
% 0.19/0.49    k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) != k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))) | ~r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))),
% 0.19/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.49  fof(f665,plain,(
% 0.19/0.49    spl7_74 | ~spl7_44),
% 0.19/0.49    inference(avatar_split_clause,[],[f609,f383,f661])).
% 0.19/0.49  fof(f661,plain,(
% 0.19/0.49    spl7_74 <=> k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).
% 0.19/0.49  fof(f383,plain,(
% 0.19/0.49    spl7_44 <=> r2_hidden(sK3(sK0,sK0,sK1,sK2),sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.19/0.49  fof(f609,plain,(
% 0.19/0.49    k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) | ~spl7_44),
% 0.19/0.49    inference(resolution,[],[f385,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X3] : (~r2_hidden(X3,sK0) | k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    (~r2_relset_1(sK0,sK0,sK1,sK2) & ! [X3] : (k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3) | ~r2_hidden(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & ! [X3] : (k11_relat_1(X2,X3) = k11_relat_1(sK1,X3) | ~r2_hidden(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & ! [X3] : (k11_relat_1(X2,X3) = k11_relat_1(sK1,X3) | ~r2_hidden(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) => (~r2_relset_1(sK0,sK0,sK1,sK2) & ! [X3] : (k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3) | ~r2_hidden(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.19/0.49    inference(flattening,[],[f9])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 0.19/0.49    inference(negated_conjecture,[],[f7])).
% 0.19/0.49  fof(f7,conjecture,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).
% 0.19/0.49  fof(f385,plain,(
% 0.19/0.49    r2_hidden(sK3(sK0,sK0,sK1,sK2),sK0) | ~spl7_44),
% 0.19/0.49    inference(avatar_component_clause,[],[f383])).
% 0.19/0.49  fof(f399,plain,(
% 0.19/0.49    spl7_10 | ~spl7_3 | ~spl7_8),
% 0.19/0.49    inference(avatar_split_clause,[],[f234,f90,f60,f110])).
% 0.19/0.49  fof(f110,plain,(
% 0.19/0.49    spl7_10 <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    spl7_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.19/0.49  fof(f90,plain,(
% 0.19/0.49    spl7_8 <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.19/0.49  fof(f234,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0)) | (~spl7_3 | ~spl7_8)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f62,f92,f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | ~spl7_8),
% 0.19/0.49    inference(avatar_component_clause,[],[f90])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f60])).
% 0.19/0.49  fof(f393,plain,(
% 0.19/0.49    spl7_44 | ~spl7_10),
% 0.19/0.49    inference(avatar_split_clause,[],[f330,f110,f383])).
% 0.19/0.49  fof(f330,plain,(
% 0.19/0.49    r2_hidden(sK3(sK0,sK0,sK1,sK2),sK0) | ~spl7_10),
% 0.19/0.49    inference(resolution,[],[f112,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.49    inference(flattening,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.49    inference(nnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.19/0.49  fof(f112,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0)) | ~spl7_10),
% 0.19/0.49    inference(avatar_component_clause,[],[f110])).
% 0.19/0.49  fof(f207,plain,(
% 0.19/0.49    ~spl7_8 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_9),
% 0.19/0.49    inference(avatar_split_clause,[],[f98,f94,f60,f55,f50,f90])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    spl7_1 <=> r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    spl7_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.19/0.49  fof(f94,plain,(
% 0.19/0.49    spl7_9 <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.19/0.49  fof(f98,plain,(
% 0.19/0.49    ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_9)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f52,f62,f57,f96,f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_relset_1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & m1_subset_1(sK4(X0,X1,X2,X3),X1)) & m1_subset_1(sK3(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f22,f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK3(X0,X1,X2,X3),X0)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & m1_subset_1(sK4(X0,X1,X2,X3),X1)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(rectify,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(flattening,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(nnf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).
% 0.19/0.49  fof(f96,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | ~spl7_9),
% 0.19/0.49    inference(avatar_component_clause,[],[f94])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f55])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ~r2_relset_1(sK0,sK0,sK1,sK2) | spl7_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f50])).
% 0.19/0.49  fof(f206,plain,(
% 0.19/0.49    spl7_9 | ~spl7_5 | ~spl7_12),
% 0.19/0.49    inference(avatar_split_clause,[],[f164,f121,f72,f94])).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    spl7_5 <=> v1_relat_1(sK2)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.19/0.49  fof(f121,plain,(
% 0.19/0.49    spl7_12 <=> r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.19/0.49  fof(f164,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | (~spl7_5 | ~spl7_12)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f74,f123,f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(nnf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.19/0.49  fof(f123,plain,(
% 0.19/0.49    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))) | ~spl7_12),
% 0.19/0.49    inference(avatar_component_clause,[],[f121])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    v1_relat_1(sK2) | ~spl7_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f72])).
% 0.19/0.49  fof(f205,plain,(
% 0.19/0.49    ~spl7_4 | spl7_14 | ~spl7_8),
% 0.19/0.49    inference(avatar_split_clause,[],[f195,f90,f141,f67])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    spl7_4 <=> v1_relat_1(sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.19/0.49  fof(f141,plain,(
% 0.19/0.49    spl7_14 <=> r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.19/0.49  fof(f195,plain,(
% 0.19/0.49    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | ~v1_relat_1(sK1) | ~spl7_8),
% 0.19/0.49    inference(resolution,[],[f92,f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f144,plain,(
% 0.19/0.49    ~spl7_14 | ~spl7_4 | spl7_8),
% 0.19/0.49    inference(avatar_split_clause,[],[f131,f90,f67,f141])).
% 0.19/0.49  fof(f131,plain,(
% 0.19/0.49    ~r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | (~spl7_4 | spl7_8)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f69,f91,f38])).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | spl7_8),
% 0.19/0.49    inference(avatar_component_clause,[],[f90])).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    v1_relat_1(sK1) | ~spl7_4),
% 0.19/0.49    inference(avatar_component_clause,[],[f67])).
% 0.19/0.49  fof(f127,plain,(
% 0.19/0.49    ~spl7_5 | spl7_12 | ~spl7_9),
% 0.19/0.49    inference(avatar_split_clause,[],[f106,f94,f121,f72])).
% 0.19/0.49  fof(f106,plain,(
% 0.19/0.49    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))) | ~v1_relat_1(sK2) | ~spl7_9),
% 0.19/0.49    inference(resolution,[],[f96,f37])).
% 0.19/0.49  fof(f113,plain,(
% 0.19/0.49    spl7_10 | ~spl7_2 | ~spl7_9),
% 0.19/0.49    inference(avatar_split_clause,[],[f102,f94,f55,f110])).
% 0.19/0.49  fof(f102,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0)) | (~spl7_2 | ~spl7_9)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f57,f96,f42])).
% 0.19/0.49  fof(f97,plain,(
% 0.19/0.49    ~spl7_3 | ~spl7_2 | spl7_8 | spl7_9 | spl7_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f88,f50,f94,f90,f55,f60])).
% 0.19/0.49  fof(f88,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl7_1),
% 0.19/0.49    inference(resolution,[],[f35,f52])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    spl7_5 | ~spl7_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f64,f55,f72])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    v1_relat_1(sK2) | ~spl7_2),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f44,f57,f43])).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    spl7_4 | ~spl7_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f65,f60,f67])).
% 0.19/0.49  fof(f65,plain,(
% 0.19/0.49    v1_relat_1(sK1) | ~spl7_3),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f44,f62,f43])).
% 0.19/0.49  fof(f63,plain,(
% 0.19/0.49    spl7_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f27,f60])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    spl7_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f28,f55])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    ~spl7_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f30,f50])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ~r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (8108)------------------------------
% 0.19/0.49  % (8108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (8108)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (8108)Memory used [KB]: 11129
% 0.19/0.49  % (8108)Time elapsed: 0.073 s
% 0.19/0.49  % (8108)------------------------------
% 0.19/0.49  % (8108)------------------------------
% 0.19/0.49  % (8098)Success in time 0.142 s
%------------------------------------------------------------------------------
