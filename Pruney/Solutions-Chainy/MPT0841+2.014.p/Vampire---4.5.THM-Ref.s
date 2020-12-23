%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 239 expanded)
%              Number of leaves         :   20 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  403 (1585 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f78,f119,f214])).

fof(f214,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f212,f84])).

fof(f84,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f83,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK5,sK4),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f23,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X5,X4),X3)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X6,X4),X3)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X5,X4),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X6,X4),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X5,X4),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X6,X4),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(X6,sK4),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(X6,sK4),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK5,sK4),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X6,X4),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X5,X4),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f212,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f211,f121])).

fof(f121,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f120,f38])).

fof(f120,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_1 ),
    inference(superposition,[],[f70,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f70,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl10_1
  <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f211,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f199,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
            & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f151,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f123,f84])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3) )
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl10_2
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f151,plain,(
    ! [X10,X11] :
      ( m1_subset_1(sK9(X10,X11,sK3),sK2)
      | ~ r2_hidden(X10,k9_relat_1(sK3,X11)) ) ),
    inference(subsumption_resolution,[],[f136,f84])).

fof(f136,plain,(
    ! [X10,X11] :
      ( m1_subset_1(sK9(X10,X11,sK3),sK2)
      | ~ r2_hidden(X10,k9_relat_1(sK3,X11))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f100,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | m1_subset_1(X0,sK2) ) ),
    inference(resolution,[],[f91,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f91,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f89,f38])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f119,plain,
    ( spl10_1
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f117,f73])).

fof(f73,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl10_3
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f117,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f97,f93])).

fof(f93,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f92,f38])).

fof(f92,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl10_1 ),
    inference(superposition,[],[f65,f59])).

fof(f65,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f97,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK5,X0) )
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f94,f84])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3) )
    | ~ spl10_4 ),
    inference(resolution,[],[f60,f77])).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl10_4
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f60,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ r2_hidden(X7,X1)
      | r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f78,plain,
    ( spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f41,f76,f64])).

fof(f41,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f42,f72,f64])).

fof(f42,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f43,f67,f64])).

fof(f43,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:30:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (12228)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (12226)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (12234)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (12228)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (12237)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f69,f74,f78,f119,f214])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ~spl10_1 | ~spl10_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f213])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    $false | (~spl10_1 | ~spl10_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f212,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.21/0.49    inference(resolution,[],[f44,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & ((r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK5,sK4),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(sK4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f23,f26,f25,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(X4,sK0)) => ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,sK4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(sK4,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,sK4),sK3) & m1_subset_1(X6,sK2)) => (r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK5,sK4),sK3) & m1_subset_1(sK5,sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f211,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~spl10_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f38])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_1),
% 0.21/0.49    inference(superposition,[],[f70,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | ~spl10_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl10_1 <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~spl10_2),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~spl10_2),
% 0.21/0.49    inference(resolution,[],[f199,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(rectify,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | ~spl10_2),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f198])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | ~spl10_2),
% 0.21/0.49    inference(resolution,[],[f151,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | ~spl10_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f84])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) ) | ~spl10_2),
% 0.21/0.49    inference(resolution,[],[f68,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X5] : (~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1)) ) | ~spl10_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl10_2 <=> ! [X5] : (~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X10,X11] : (m1_subset_1(sK9(X10,X11,sK3),sK2) | ~r2_hidden(X10,k9_relat_1(sK3,X11))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f136,f84])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X10,X11] : (m1_subset_1(sK9(X10,X11,sK3),sK2) | ~r2_hidden(X10,k9_relat_1(sK3,X11)) | ~v1_relat_1(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f100,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(X0,sK2)) )),
% 0.21/0.49    inference(resolution,[],[f91,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.50    inference(resolution,[],[f89,f38])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(superposition,[],[f57,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl10_1 | ~spl10_3 | ~spl10_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    $false | (spl10_1 | ~spl10_3 | ~spl10_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f117,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    r2_hidden(sK5,sK1) | ~spl10_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl10_3 <=> r2_hidden(sK5,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~r2_hidden(sK5,sK1) | (spl10_1 | ~spl10_4)),
% 0.21/0.50    inference(resolution,[],[f97,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | spl10_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f92,f38])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | spl10_1),
% 0.21/0.50    inference(superposition,[],[f65,f59])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | spl10_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0)) ) | ~spl10_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f94,f84])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK5,X0) | r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) ) | ~spl10_4),
% 0.21/0.50    inference(resolution,[],[f60,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl10_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl10_4 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X6,X0,X7,X1] : (~r2_hidden(k4_tarski(X7,X6),X0) | ~r2_hidden(X7,X1) | r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(rectify,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl10_1 | spl10_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f76,f64])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl10_1 | spl10_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f72,f64])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    r2_hidden(sK5,sK1) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~spl10_1 | spl10_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f67,f64])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (12228)------------------------------
% 0.21/0.50  % (12228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12228)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (12228)Memory used [KB]: 10746
% 0.21/0.50  % (12228)Time elapsed: 0.069 s
% 0.21/0.50  % (12228)------------------------------
% 0.21/0.50  % (12228)------------------------------
% 0.21/0.50  % (12225)Success in time 0.139 s
%------------------------------------------------------------------------------
