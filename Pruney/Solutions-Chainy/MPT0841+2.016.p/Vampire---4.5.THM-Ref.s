%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 731 expanded)
%              Number of leaves         :   21 ( 285 expanded)
%              Depth                    :   24
%              Number of atoms          :  556 (7227 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(subsumption_resolution,[],[f193,f159])).

fof(f159,plain,(
    m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f158,f136])).

fof(f136,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f135,f85])).

fof(f85,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f83,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(resolution,[],[f55,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
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
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f26,f32,f31,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
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
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X6,X4),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                      & m1_subset_1(X4,sK0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ! [X5] :
                          ( ~ r2_hidden(X5,X1)
                          | ~ r2_hidden(k4_tarski(X5,X4),X3)
                          | ~ m1_subset_1(X5,X2) )
                      | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                    & ( ? [X6] :
                          ( r2_hidden(X6,X1)
                          & r2_hidden(k4_tarski(X6,X4),X3)
                          & m1_subset_1(X6,X2) )
                      | r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                    & m1_subset_1(X4,sK0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ! [X5] :
                        ( ~ r2_hidden(X5,sK1)
                        | ~ r2_hidden(k4_tarski(X5,X4),X3)
                        | ~ m1_subset_1(X5,X2) )
                    | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                  & ( ? [X6] :
                        ( r2_hidden(X6,sK1)
                        & r2_hidden(k4_tarski(X6,X4),X3)
                        & m1_subset_1(X6,X2) )
                    | r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ! [X5] :
                      ( ~ r2_hidden(X5,sK1)
                      | ~ r2_hidden(k4_tarski(X5,X4),X3)
                      | ~ m1_subset_1(X5,X2) )
                  | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                & ( ? [X6] :
                      ( r2_hidden(X6,sK1)
                      & r2_hidden(k4_tarski(X6,X4),X3)
                      & m1_subset_1(X6,X2) )
                  | r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ! [X5] :
                    ( ~ r2_hidden(X5,sK1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X3)
                    | ~ m1_subset_1(X5,sK2) )
                | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
              & ( ? [X6] :
                    ( r2_hidden(X6,sK1)
                    & r2_hidden(k4_tarski(X6,X4),X3)
                    & m1_subset_1(X6,sK2) )
                | r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,sK1)
                  | ~ r2_hidden(k4_tarski(X5,X4),X3)
                  | ~ m1_subset_1(X5,sK2) )
              | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,sK1)
                  & r2_hidden(k4_tarski(X6,X4),X3)
                  & m1_subset_1(X6,sK2) )
              | r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) )
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

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(X6,sK4),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK5,sK4),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
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
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
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
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
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
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f135,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f133,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | m1_subset_1(sK5,sK2) ) ),
    inference(subsumption_resolution,[],[f132,f126])).

fof(f126,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK9(X5,X6,sK3),sK2)
      | ~ r2_hidden(X5,k9_relat_1(sK3,X6)) ) ),
    inference(subsumption_resolution,[],[f116,f85])).

fof(f116,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X6))
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK9(X5,X6,sK3),sK2) ) ),
    inference(resolution,[],[f66,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f72,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f96,f90])).

% (30698)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (30712)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (30696)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (30708)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f90,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f70,f49])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | v1_xboole_0(k2_zfmisc_1(sK2,sK0))
      | r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) ) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f69,f49])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | m1_subset_1(sK5,sK2)
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK2) ) ),
    inference(resolution,[],[f123,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f123,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK9(sK4,X1,sK3),sK2)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X1))
      | ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
      | m1_subset_1(sK5,sK2) ) ),
    inference(subsumption_resolution,[],[f113,f85])).

fof(f113,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X1))
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK9(sK4,X1,sK3),sK2)
      | ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
      | m1_subset_1(sK5,sK2) ) ),
    inference(resolution,[],[f66,f80])).

fof(f80,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK4),sK3)
      | ~ m1_subset_1(X2,sK2)
      | ~ r2_hidden(X2,sK1)
      | m1_subset_1(sK5,sK2) ) ),
    inference(resolution,[],[f54,f51])).

fof(f51,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f158,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f153,f49])).

fof(f153,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f193,plain,(
    ~ m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f187,f157])).

fof(f157,plain,(
    r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f156,f141])).

fof(f141,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f140,f85])).

fof(f140,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f138,f67])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | r2_hidden(sK5,sK1) ) ),
    inference(subsumption_resolution,[],[f137,f126])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | r2_hidden(sK5,sK1)
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK2) ) ),
    inference(resolution,[],[f124,f63])).

fof(f124,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK9(sK4,X2,sK3),sK2)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X2))
      | ~ r2_hidden(sK9(sK4,X2,sK3),sK1)
      | r2_hidden(sK5,sK1) ) ),
    inference(subsumption_resolution,[],[f114,f85])).

fof(f114,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X2))
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK9(sK4,X2,sK3),sK2)
      | ~ r2_hidden(sK9(sK4,X2,sK3),sK1)
      | r2_hidden(sK5,sK1) ) ),
    inference(resolution,[],[f66,f79])).

fof(f79,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK4),sK3)
      | ~ m1_subset_1(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(sK5,sK1) ) ),
    inference(resolution,[],[f54,f53])).

fof(f53,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f156,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f152,f49])).

fof(f152,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f53,f71])).

fof(f187,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK5,sK2) ),
    inference(resolution,[],[f184,f175])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f174,f85])).

fof(f174,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(condensation,[],[f169])).

fof(f169,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK1)
      | ~ r2_hidden(k4_tarski(X8,sK4),sK3)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(k4_tarski(X9,sK4),sK3)
      | ~ m1_subset_1(X9,sK2)
      | ~ r2_hidden(X9,sK1) ) ),
    inference(resolution,[],[f75,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f150,f49])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    inference(superposition,[],[f54,f71])).

fof(f75,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f38,f37,f36])).

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f184,plain,(
    r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(resolution,[],[f183,f155])).

fof(f155,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f151,f49])).

fof(f151,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f52,f71])).

fof(f52,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f183,plain,(
    ~ r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f182,f85])).

fof(f182,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f180,f67])).

fof(f180,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f179,f126])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK2) ) ),
    inference(resolution,[],[f178,f63])).

fof(f178,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK9(sK4,X1,sK3),sK2)
      | ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f177,f85])).

fof(f177,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
      | ~ m1_subset_1(sK9(sK4,X1,sK3),sK2)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X1))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f175,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.42  % (30702)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.43  % (30694)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.45  % (30711)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.45  % (30697)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.46  % (30693)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.46  % (30703)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % (30705)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.47  % (30701)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.47  % (30695)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.48  % (30690)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (30691)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.48  % (30692)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.49  % (30706)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.49  % (30709)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.49  % (30689)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (30700)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.49  % (30710)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.50  % (30710)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f194,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f193,f159])).
% 0.19/0.50  fof(f159,plain,(
% 0.19/0.50    m1_subset_1(sK5,sK2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f158,f136])).
% 0.19/0.50  fof(f136,plain,(
% 0.19/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f135,f85])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    v1_relat_1(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f83,f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.50  fof(f83,plain,(
% 0.19/0.50    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.19/0.50    inference(resolution,[],[f55,f49])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    (((((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & ((r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK5,sK4),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(sK4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f26,f32,f31,f30,f29,f28,f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1))) & m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1))) & m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) & ~v1_xboole_0(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(X4,sK0)) => ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,sK4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(sK4,sK0))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,sK4),sK3) & m1_subset_1(X6,sK2)) => (r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK5,sK4),sK3) & m1_subset_1(sK5,sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.50    inference(rectify,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.50    inference(flattening,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.50    inference(nnf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,negated_conjecture,(
% 0.19/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f11])).
% 0.19/0.50  fof(f11,conjecture,(
% 0.19/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.50  fof(f135,plain,(
% 0.19/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2) | ~v1_relat_1(sK3)),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f134])).
% 0.19/0.50  fof(f134,plain,(
% 0.19/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.19/0.50    inference(resolution,[],[f133,f67])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.50    inference(rectify,[],[f40])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.50    inference(nnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.19/0.50  fof(f133,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | m1_subset_1(sK5,sK2)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f132,f126])).
% 0.19/0.50  fof(f126,plain,(
% 0.19/0.50    ( ! [X6,X5] : (r2_hidden(sK9(X5,X6,sK3),sK2) | ~r2_hidden(X5,k9_relat_1(sK3,X6))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f116,f85])).
% 0.19/0.50  fof(f116,plain,(
% 0.19/0.50    ( ! [X6,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X6)) | ~v1_relat_1(sK3) | r2_hidden(sK9(X5,X6,sK3),sK2)) )),
% 0.19/0.50    inference(resolution,[],[f66,f98])).
% 0.19/0.50  fof(f98,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK2)) )),
% 0.19/0.50    inference(resolution,[],[f72,f97])).
% 0.19/0.50  fof(f97,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) | ~r2_hidden(X0,sK3)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f96,f90])).
% 0.19/0.50  % (30698)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.50  % (30712)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.50  % (30696)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.51  % (30708)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(sK2,sK0)) | ~r2_hidden(X0,sK3)) )),
% 0.19/0.51    inference(resolution,[],[f70,f49])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,sK3) | v1_xboole_0(k2_zfmisc_1(sK2,sK0)) | r2_hidden(X0,k2_zfmisc_1(sK2,sK0))) )),
% 0.19/0.51    inference(resolution,[],[f94,f64])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(X0,k2_zfmisc_1(sK2,sK0)) | ~r2_hidden(X0,sK3)) )),
% 0.19/0.51    inference(resolution,[],[f69,f49])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.51    inference(flattening,[],[f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.51    inference(nnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f43])).
% 0.19/0.51  fof(f132,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | m1_subset_1(sK5,sK2) | ~r2_hidden(sK9(sK4,X0,sK3),sK2)) )),
% 0.19/0.51    inference(resolution,[],[f123,f63])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.51  fof(f123,plain,(
% 0.19/0.51    ( ! [X1] : (~m1_subset_1(sK9(sK4,X1,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X1)) | ~r2_hidden(sK9(sK4,X1,sK3),sK1) | m1_subset_1(sK5,sK2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f113,f85])).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    ( ! [X1] : (~r2_hidden(sK4,k9_relat_1(sK3,X1)) | ~v1_relat_1(sK3) | ~m1_subset_1(sK9(sK4,X1,sK3),sK2) | ~r2_hidden(sK9(sK4,X1,sK3),sK1) | m1_subset_1(sK5,sK2)) )),
% 0.19/0.51    inference(resolution,[],[f66,f80])).
% 0.19/0.51  fof(f80,plain,(
% 0.19/0.51    ( ! [X2] : (~r2_hidden(k4_tarski(X2,sK4),sK3) | ~m1_subset_1(X2,sK2) | ~r2_hidden(X2,sK1) | m1_subset_1(sK5,sK2)) )),
% 0.19/0.51    inference(resolution,[],[f54,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | m1_subset_1(sK5,sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X5] : (~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f158,plain,(
% 0.19/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f153,f49])).
% 0.19/0.51  fof(f153,plain,(
% 0.19/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.51    inference(superposition,[],[f51,f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.51  fof(f193,plain,(
% 0.19/0.51    ~m1_subset_1(sK5,sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f187,f157])).
% 0.19/0.51  fof(f157,plain,(
% 0.19/0.51    r2_hidden(sK5,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f156,f141])).
% 0.19/0.51  fof(f141,plain,(
% 0.19/0.51    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f140,f85])).
% 0.19/0.51  fof(f140,plain,(
% 0.19/0.51    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1) | ~v1_relat_1(sK3)),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f139])).
% 0.19/0.51  fof(f139,plain,(
% 0.19/0.51    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.19/0.51    inference(resolution,[],[f138,f67])).
% 0.19/0.51  fof(f138,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | r2_hidden(sK5,sK1)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f137,f126])).
% 0.19/0.51  fof(f137,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | r2_hidden(sK5,sK1) | ~r2_hidden(sK9(sK4,X0,sK3),sK2)) )),
% 0.19/0.51    inference(resolution,[],[f124,f63])).
% 0.19/0.51  fof(f124,plain,(
% 0.19/0.51    ( ! [X2] : (~m1_subset_1(sK9(sK4,X2,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X2)) | ~r2_hidden(sK9(sK4,X2,sK3),sK1) | r2_hidden(sK5,sK1)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f114,f85])).
% 0.19/0.51  fof(f114,plain,(
% 0.19/0.51    ( ! [X2] : (~r2_hidden(sK4,k9_relat_1(sK3,X2)) | ~v1_relat_1(sK3) | ~m1_subset_1(sK9(sK4,X2,sK3),sK2) | ~r2_hidden(sK9(sK4,X2,sK3),sK1) | r2_hidden(sK5,sK1)) )),
% 0.19/0.51    inference(resolution,[],[f66,f79])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK4),sK3) | ~m1_subset_1(X1,sK2) | ~r2_hidden(X1,sK1) | r2_hidden(sK5,sK1)) )),
% 0.19/0.51    inference(resolution,[],[f54,f53])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f156,plain,(
% 0.19/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f152,f49])).
% 0.19/0.51  fof(f152,plain,(
% 0.19/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.51    inference(superposition,[],[f53,f71])).
% 0.19/0.51  fof(f187,plain,(
% 0.19/0.51    ~r2_hidden(sK5,sK1) | ~m1_subset_1(sK5,sK2)),
% 0.19/0.51    inference(resolution,[],[f184,f175])).
% 0.19/0.51  fof(f175,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,sK2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f174,f85])).
% 0.19/0.51  fof(f174,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~v1_relat_1(sK3) | ~m1_subset_1(X0,sK2)) )),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f173])).
% 0.19/0.52  fof(f173,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~m1_subset_1(X0,sK2)) )),
% 0.19/0.52    inference(condensation,[],[f169])).
% 0.19/0.52  fof(f169,plain,(
% 0.19/0.52    ( ! [X8,X9] : (~r2_hidden(X8,sK1) | ~r2_hidden(k4_tarski(X8,sK4),sK3) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(X9,sK4),sK3) | ~m1_subset_1(X9,sK2) | ~r2_hidden(X9,sK1)) )),
% 0.19/0.52    inference(resolution,[],[f75,f154])).
% 0.19/0.52  fof(f154,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~m1_subset_1(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f150,f49])).
% 0.19/0.52  fof(f150,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~m1_subset_1(X0,sK2) | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) )),
% 0.19/0.52    inference(superposition,[],[f54,f71])).
% 0.19/0.52  fof(f75,plain,(
% 0.19/0.52    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f58])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f38,f37,f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(rectify,[],[f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.19/0.52  fof(f184,plain,(
% 0.19/0.52    r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.19/0.52    inference(resolution,[],[f183,f155])).
% 0.19/0.52  fof(f155,plain,(
% 0.19/0.52    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.19/0.52    inference(subsumption_resolution,[],[f151,f49])).
% 0.19/0.52  fof(f151,plain,(
% 0.19/0.52    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.52    inference(superposition,[],[f52,f71])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.19/0.52    inference(cnf_transformation,[],[f33])).
% 0.19/0.52  fof(f183,plain,(
% 0.19/0.52    ~r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.19/0.52    inference(subsumption_resolution,[],[f182,f85])).
% 0.19/0.52  fof(f182,plain,(
% 0.19/0.52    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f181])).
% 0.19/0.52  fof(f181,plain,(
% 0.19/0.52    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.19/0.52    inference(resolution,[],[f180,f67])).
% 0.19/0.52  fof(f180,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f179,f126])).
% 0.19/0.52  fof(f179,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK2)) )),
% 0.19/0.52    inference(resolution,[],[f178,f63])).
% 0.19/0.52  fof(f178,plain,(
% 0.19/0.52    ( ! [X1] : (~m1_subset_1(sK9(sK4,X1,sK3),sK2) | ~r2_hidden(sK9(sK4,X1,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f177,f85])).
% 0.19/0.52  fof(f177,plain,(
% 0.19/0.52    ( ! [X1] : (~r2_hidden(sK9(sK4,X1,sK3),sK1) | ~m1_subset_1(sK9(sK4,X1,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X1)) | ~v1_relat_1(sK3)) )),
% 0.19/0.52    inference(resolution,[],[f175,f66])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (30710)------------------------------
% 0.19/0.52  % (30710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (30710)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (30710)Memory used [KB]: 1791
% 0.19/0.52  % (30710)Time elapsed: 0.109 s
% 0.19/0.52  % (30710)------------------------------
% 0.19/0.52  % (30710)------------------------------
% 0.19/0.52  % (30682)Success in time 0.176 s
%------------------------------------------------------------------------------
