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
% DateTime   : Thu Dec  3 12:57:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 212 expanded)
%              Number of leaves         :   24 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  387 (1246 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f161,f282,f303])).

fof(f303,plain,
    ( spl8_7
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f302,f82,f78,f154])).

fof(f154,plain,
    ( spl8_7
  <=> ! [X1] : ~ v4_relat_1(sK4,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f78,plain,
    ( spl8_1
  <=> r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f82,plain,
    ( spl8_2
  <=> ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK5),sK4)
        | ~ m1_subset_1(X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f302,plain,
    ( ! [X0] : ~ v4_relat_1(sK4,X0)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f301,f95])).

fof(f95,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f67,f49])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK5),sK4)
          | ~ m1_subset_1(X4,sK3) )
      | ~ r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) )
    & ( ( r2_hidden(k4_tarski(sK6,sK5),sK4)
        & m1_subset_1(sK6,sK3) )
      | r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f30,f35,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X5,X3),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,sK2,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,sK2,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                      | ~ m1_subset_1(X4,X1) )
                  | ~ r2_hidden(X3,k2_relset_1(X1,sK2,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X5,X3),X2)
                      & m1_subset_1(X5,X1) )
                  | r2_hidden(X3,k2_relset_1(X1,sK2,X2)) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                    | ~ m1_subset_1(X4,sK3) )
                | ~ r2_hidden(X3,k2_relset_1(sK3,sK2,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X5,X3),X2)
                    & m1_subset_1(X5,sK3) )
                | r2_hidden(X3,k2_relset_1(sK3,sK2,X2)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                  | ~ m1_subset_1(X4,sK3) )
              | ~ r2_hidden(X3,k2_relset_1(sK3,sK2,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),X2)
                  & m1_subset_1(X5,sK3) )
              | r2_hidden(X3,k2_relset_1(sK3,sK2,X2)) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),sK4)
                | ~ m1_subset_1(X4,sK3) )
            | ~ r2_hidden(X3,k2_relset_1(sK3,sK2,sK4)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),sK4)
                & m1_subset_1(X5,sK3) )
            | r2_hidden(X3,k2_relset_1(sK3,sK2,sK4)) ) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X3),sK4)
              | ~ m1_subset_1(X4,sK3) )
          | ~ r2_hidden(X3,k2_relset_1(sK3,sK2,sK4)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,X3),sK4)
              & m1_subset_1(X5,sK3) )
          | r2_hidden(X3,k2_relset_1(sK3,sK2,sK4)) ) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK5),sK4)
            | ~ m1_subset_1(X4,sK3) )
        | ~ r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,sK5),sK4)
            & m1_subset_1(X5,sK3) )
        | r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(X5,sK5),sK4)
        & m1_subset_1(X5,sK3) )
   => ( r2_hidden(k4_tarski(sK6,sK5),sK4)
      & m1_subset_1(sK6,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f301,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK4)
        | ~ v4_relat_1(sK4,X0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f297,f293])).

fof(f293,plain,
    ( r2_hidden(sK5,k2_relat_1(sK4))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f284,f49])).

fof(f284,plain,
    ( r2_hidden(sK5,k2_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ spl8_1 ),
    inference(superposition,[],[f79,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f79,plain,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,k2_relat_1(sK4))
        | ~ v1_relat_1(sK4)
        | ~ v4_relat_1(sK4,X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f296,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f124,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f20,f27,f26])).

fof(f26,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X3,X0),X2)
          & r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
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

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP0(X1,X0,X2)
      | ~ sP1(X2,X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(superposition,[],[f60,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f53,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X1,X2))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f296,plain,
    ( ! [X0] : ~ sP0(X0,sK4,sK5)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f295,f117])).

fof(f117,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK7(X10,sK4,X11),sK3)
      | ~ sP0(X10,sK4,X11) ) ),
    inference(resolution,[],[f63,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f72,f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK3,sK2))
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ( r2_hidden(sK7(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1)
          & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X2),X1)
          & r2_hidden(X4,k1_relat_1(X1)) )
     => ( r2_hidden(sK7(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,X2),X1)
            & r2_hidden(X4,k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ sP0(X0,sK4,sK5)
        | ~ r2_hidden(sK7(X0,sK4,sK5),sK3) )
    | ~ spl8_2 ),
    inference(resolution,[],[f286,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f286,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(X0,sK4,sK5),sK3)
        | ~ sP0(X0,sK4,sK5) )
    | ~ spl8_2 ),
    inference(resolution,[],[f83,f63])).

fof(f83,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK5),sK4)
        | ~ m1_subset_1(X4,sK3) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f282,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f280,f131])).

fof(f131,plain,
    ( ~ r2_hidden(sK5,k2_relat_1(sK4))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f130,plain,
    ( ~ r2_hidden(sK5,k2_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | spl8_1 ),
    inference(superposition,[],[f80,f68])).

fof(f80,plain,
    ( ~ r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f280,plain,
    ( r2_hidden(sK5,k2_relat_1(sK4))
    | ~ spl8_3 ),
    inference(resolution,[],[f278,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f278,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK4),X0)
        | r2_hidden(sK5,X0) )
    | ~ spl8_3 ),
    inference(resolution,[],[f273,f88])).

fof(f88,plain,
    ( r2_hidden(k4_tarski(sK6,sK5),sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_3
  <=> r2_hidden(k4_tarski(sK6,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f273,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
      | ~ r1_tarski(k2_relat_1(sK4),X2)
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f269,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f269,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k2_zfmisc_1(sK3,X0))
      | ~ r2_hidden(X1,sK4)
      | ~ r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(resolution,[],[f167,f49])).

fof(f167,plain,(
    ! [X14,X12,X15,X13,X16] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ r1_tarski(k2_relat_1(X12),X13)
      | ~ r2_hidden(X16,X12)
      | r2_hidden(X16,k2_zfmisc_1(X14,X13)) ) ),
    inference(resolution,[],[f71,f55])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f161,plain,(
    ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f98,f155])).

fof(f155,plain,
    ( ! [X1] : ~ v4_relat_1(sK4,X1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f98,plain,(
    v4_relat_1(sK4,sK3) ),
    inference(resolution,[],[f69,f49])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f89,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f51,f86,f78])).

fof(f51,plain,
    ( r2_hidden(k4_tarski(sK6,sK5),sK4)
    | r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f52,f82,f78])).

fof(f52,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK5),sK4)
      | ~ m1_subset_1(X4,sK3)
      | ~ r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:17:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (1488)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (1488)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f84,f89,f161,f282,f303])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    spl8_7 | ~spl8_1 | ~spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f302,f82,f78,f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl8_7 <=> ! [X1] : ~v4_relat_1(sK4,X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl8_1 <=> r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl8_2 <=> ! [X4] : (~r2_hidden(k4_tarski(X4,sK5),sK4) | ~m1_subset_1(X4,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_relat_1(sK4,X0)) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f301,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    v1_relat_1(sK4)),
% 0.21/0.49    inference(resolution,[],[f67,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ((((! [X4] : (~r2_hidden(k4_tarski(X4,sK5),sK4) | ~m1_subset_1(X4,sK3)) | ~r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4))) & ((r2_hidden(k4_tarski(sK6,sK5),sK4) & m1_subset_1(sK6,sK3)) | r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f30,f35,f34,f33,f32,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,sK2,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,sK2,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,sK2,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,sK2,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,sK3)) | ~r2_hidden(X3,k2_relset_1(sK3,sK2,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,sK3)) | r2_hidden(X3,k2_relset_1(sK3,sK2,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))) & ~v1_xboole_0(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,sK3)) | ~r2_hidden(X3,k2_relset_1(sK3,sK2,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,sK3)) | r2_hidden(X3,k2_relset_1(sK3,sK2,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK4) | ~m1_subset_1(X4,sK3)) | ~r2_hidden(X3,k2_relset_1(sK3,sK2,sK4))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK4) & m1_subset_1(X5,sK3)) | r2_hidden(X3,k2_relset_1(sK3,sK2,sK4)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK4) | ~m1_subset_1(X4,sK3)) | ~r2_hidden(X3,k2_relset_1(sK3,sK2,sK4))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK4) & m1_subset_1(X5,sK3)) | r2_hidden(X3,k2_relset_1(sK3,sK2,sK4)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK5),sK4) | ~m1_subset_1(X4,sK3)) | ~r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK5),sK4) & m1_subset_1(X5,sK3)) | r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ? [X5] : (r2_hidden(k4_tarski(X5,sK5),sK4) & m1_subset_1(X5,sK3)) => (r2_hidden(k4_tarski(sK6,sK5),sK4) & m1_subset_1(sK6,sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(rectify,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(sK4) | ~v4_relat_1(sK4,X0)) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f297,f293])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    r2_hidden(sK5,k2_relat_1(sK4)) | ~spl8_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f284,f49])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    r2_hidden(sK5,k2_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~spl8_1),
% 0.21/0.49    inference(superposition,[],[f79,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) | ~spl8_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK5,k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v4_relat_1(sK4,X0)) ) | ~spl8_2),
% 0.21/0.49    inference(resolution,[],[f296,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | ~r2_hidden(X2,k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(definition_folding,[],[f20,f27,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X2,X1] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(X0)) | sP0(X1,X0,X2) | ~sP1(X2,X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.49    inference(superposition,[],[f60,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(superposition,[],[f53,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X1,X2)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,k9_relat_1(X1,X2)))) | ~sP1(X0,X1,X2))),
% 0.21/0.49    inference(rectify,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X2,X1] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~sP1(X0,X2,X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f27])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0,sK4,sK5)) ) | ~spl8_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f295,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X10,X11] : (r2_hidden(sK7(X10,sK4,X11),sK3) | ~sP0(X10,sK4,X11)) )),
% 0.21/0.49    inference(resolution,[],[f63,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK4) | r2_hidden(X0,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f72,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK3,sK2)) | ~r2_hidden(X0,sK4)) )),
% 0.21/0.49    inference(resolution,[],[f55,f49])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.49    inference(flattening,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) => (r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.49    inference(rectify,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~sP0(X1,X2,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0,sK4,sK5) | ~r2_hidden(sK7(X0,sK4,sK5),sK3)) ) | ~spl8_2),
% 0.21/0.49    inference(resolution,[],[f286,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK7(X0,sK4,sK5),sK3) | ~sP0(X0,sK4,sK5)) ) | ~spl8_2),
% 0.21/0.49    inference(resolution,[],[f83,f63])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK5),sK4) | ~m1_subset_1(X4,sK3)) ) | ~spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    spl8_1 | ~spl8_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f281])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    $false | (spl8_1 | ~spl8_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f280,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k2_relat_1(sK4)) | spl8_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f49])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k2_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | spl8_1),
% 0.21/0.49    inference(superposition,[],[f80,f68])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4)) | spl8_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    r2_hidden(sK5,k2_relat_1(sK4)) | ~spl8_3),
% 0.21/0.49    inference(resolution,[],[f278,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | r2_hidden(sK5,X0)) ) | ~spl8_3),
% 0.21/0.49    inference(resolution,[],[f273,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK6,sK5),sK4) | ~spl8_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl8_3 <=> r2_hidden(k4_tarski(sK6,sK5),sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK4) | ~r1_tarski(k2_relat_1(sK4),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.49    inference(resolution,[],[f269,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,k2_zfmisc_1(sK3,X0)) | ~r2_hidden(X1,sK4) | ~r1_tarski(k2_relat_1(sK4),X0)) )),
% 0.21/0.49    inference(resolution,[],[f167,f49])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X14,X12,X15,X13,X16] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | ~r1_tarski(k2_relat_1(X12),X13) | ~r2_hidden(X16,X12) | r2_hidden(X16,k2_zfmisc_1(X14,X13))) )),
% 0.21/0.49    inference(resolution,[],[f71,f55])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ~spl8_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    $false | ~spl8_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ( ! [X1] : (~v4_relat_1(sK4,X1)) ) | ~spl8_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    v4_relat_1(sK4,sK3)),
% 0.21/0.49    inference(resolution,[],[f69,f49])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl8_1 | spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f86,f78])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK6,sK5),sK4) | r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4))),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~spl8_1 | spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f82,f78])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK5),sK4) | ~m1_subset_1(X4,sK3) | ~r2_hidden(sK5,k2_relset_1(sK3,sK2,sK4))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1488)------------------------------
% 0.21/0.49  % (1488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1488)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1488)Memory used [KB]: 6268
% 0.21/0.49  % (1488)Time elapsed: 0.042 s
% 0.21/0.49  % (1488)------------------------------
% 0.21/0.49  % (1488)------------------------------
% 0.21/0.49  % (1483)Success in time 0.128 s
%------------------------------------------------------------------------------
