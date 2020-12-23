%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t51_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:11 EDT 2019

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 613 expanded)
%              Number of leaves         :   33 ( 274 expanded)
%              Depth                    :   18
%              Number of atoms          :  667 (5945 expanded)
%              Number of equality atoms :   15 (  70 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6651,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f117,f121,f174,f249,f253,f803,f907,f6558,f6650])).

fof(f6650,plain,
    ( ~ spl14_0
    | ~ spl14_22 ),
    inference(avatar_contradiction_clause,[],[f6649])).

fof(f6649,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_22 ),
    inference(subsumption_resolution,[],[f6636,f888])).

fof(f888,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f887,f155])).

fof(f155,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f91,f70])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ! [X7] :
          ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
          | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
          | ~ m1_subset_1(X7,sK1) )
      | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
    & ( ( r2_hidden(k4_tarski(sK7,sK6),sK4)
        & r2_hidden(k4_tarski(sK5,sK7),sK3)
        & m1_subset_1(sK7,sK1) )
      | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f46,f53,f52,f51,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5,X6] :
                            ( ( ! [X7] :
                                  ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                  | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                  | ~ m1_subset_1(X7,X1) )
                              | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                            & ( ? [X8] :
                                  ( r2_hidden(k4_tarski(X8,X6),X4)
                                  & r2_hidden(k4_tarski(X5,X8),X3)
                                  & m1_subset_1(X8,X1) )
                              | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X6,X5] :
                          ( ( ! [X7] :
                                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                | ~ m1_subset_1(X7,X1) )
                            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,X1,X1,X2,X3,X4)) )
                          & ( ? [X8] :
                                ( r2_hidden(k4_tarski(X8,X6),X4)
                                & r2_hidden(k4_tarski(X5,X8),X3)
                                & m1_subset_1(X8,X1) )
                            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,X1,X1,X2,X3,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5,X6] :
                          ( ( ! [X7] :
                                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                | ~ m1_subset_1(X7,X1) )
                            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                          & ( ? [X8] :
                                ( r2_hidden(k4_tarski(X8,X6),X4)
                                & r2_hidden(k4_tarski(X5,X8),X3)
                                & m1_subset_1(X8,X1) )
                            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X6,X5] :
                        ( ( ! [X7] :
                              ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                              | ~ r2_hidden(k4_tarski(X5,X7),X3)
                              | ~ m1_subset_1(X7,sK1) )
                          | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,sK1,sK1,X2,X3,X4)) )
                        & ( ? [X8] :
                              ( r2_hidden(k4_tarski(X8,X6),X4)
                              & r2_hidden(k4_tarski(X5,X8),X3)
                              & m1_subset_1(X8,sK1) )
                          | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,sK1,sK1,X2,X3,X4)) ) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5,X6] :
                      ( ( ! [X7] :
                            ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                            | ~ r2_hidden(k4_tarski(X5,X7),X3)
                            | ~ m1_subset_1(X7,X1) )
                        | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                      & ( ? [X8] :
                            ( r2_hidden(k4_tarski(X8,X6),X4)
                            & r2_hidden(k4_tarski(X5,X8),X3)
                            & m1_subset_1(X8,X1) )
                        | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X6,X5] :
                    ( ( ! [X7] :
                          ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                          | ~ r2_hidden(k4_tarski(X5,X7),X3)
                          | ~ m1_subset_1(X7,X1) )
                      | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,sK2,X3,X4)) )
                    & ( ? [X8] :
                          ( r2_hidden(k4_tarski(X8,X6),X4)
                          & r2_hidden(k4_tarski(X5,X8),X3)
                          & m1_subset_1(X8,X1) )
                      | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,sK2,X3,X4)) ) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5,X6] :
                  ( ( ! [X7] :
                        ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                        | ~ r2_hidden(k4_tarski(X5,X7),X3)
                        | ~ m1_subset_1(X7,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                  & ( ? [X8] :
                        ( r2_hidden(k4_tarski(X8,X6),X4)
                        & r2_hidden(k4_tarski(X5,X8),X3)
                        & m1_subset_1(X8,X1) )
                    | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ? [X4] :
            ( ? [X6,X5] :
                ( ( ! [X7] :
                      ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                      | ~ r2_hidden(k4_tarski(X5,X7),sK3)
                      | ~ m1_subset_1(X7,X1) )
                  | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,sK3,X4)) )
                & ( ? [X8] :
                      ( r2_hidden(k4_tarski(X8,X6),X4)
                      & r2_hidden(k4_tarski(X5,X8),sK3)
                      & m1_subset_1(X8,X1) )
                  | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,sK3,X4)) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5,X6] :
              ( ( ! [X7] :
                    ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                    | ~ r2_hidden(k4_tarski(X5,X7),X3)
                    | ~ m1_subset_1(X7,X1) )
                | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
              & ( ? [X8] :
                    ( r2_hidden(k4_tarski(X8,X6),X4)
                    & r2_hidden(k4_tarski(X5,X8),X3)
                    & m1_subset_1(X8,X1) )
                | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ? [X6,X5] :
            ( ( ! [X7] :
                  ( ~ r2_hidden(k4_tarski(X7,X6),sK4)
                  | ~ r2_hidden(k4_tarski(X5,X7),X3)
                  | ~ m1_subset_1(X7,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,sK4)) )
            & ( ? [X8] :
                  ( r2_hidden(k4_tarski(X8,X6),sK4)
                  & r2_hidden(k4_tarski(X5,X8),X3)
                  & m1_subset_1(X8,X1) )
              | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,sK4)) ) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5,X6] :
          ( ( ! [X7] :
                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                | ~ m1_subset_1(X7,X1) )
            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
          & ( ? [X8] :
                ( r2_hidden(k4_tarski(X8,X6),X4)
                & r2_hidden(k4_tarski(X5,X8),X3)
                & m1_subset_1(X8,X1) )
            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
     => ( ( ! [X7] :
              ( ~ r2_hidden(k4_tarski(X7,sK6),X4)
              | ~ r2_hidden(k4_tarski(sK5,X7),X3)
              | ~ m1_subset_1(X7,X1) )
          | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
        & ( ? [X8] :
              ( r2_hidden(k4_tarski(X8,sK6),X4)
              & r2_hidden(k4_tarski(sK5,X8),X3)
              & m1_subset_1(X8,X1) )
          | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X6,X4,X5,X3,X1] :
      ( ? [X8] :
          ( r2_hidden(k4_tarski(X8,X6),X4)
          & r2_hidden(k4_tarski(X5,X8),X3)
          & m1_subset_1(X8,X1) )
     => ( r2_hidden(k4_tarski(sK7,X6),X4)
        & r2_hidden(k4_tarski(X5,sK7),X3)
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5,X6] :
                          ( ( ! [X7] :
                                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                | ~ m1_subset_1(X7,X1) )
                            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                          & ( ? [X8] :
                                ( r2_hidden(k4_tarski(X8,X6),X4)
                                & r2_hidden(k4_tarski(X5,X8),X3)
                                & m1_subset_1(X8,X1) )
                            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5,X6] :
                          ( ( ! [X7] :
                                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                | ~ m1_subset_1(X7,X1) )
                            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                          & ( ? [X7] :
                                ( r2_hidden(k4_tarski(X7,X6),X4)
                                & r2_hidden(k4_tarski(X5,X7),X3)
                                & m1_subset_1(X7,X1) )
                            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5,X6] :
                          ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                        <~> ? [X7] :
                              ( r2_hidden(k4_tarski(X7,X6),X4)
                              & r2_hidden(k4_tarski(X5,X7),X3)
                              & m1_subset_1(X7,X1) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                       => ! [X5,X6] :
                            ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                          <=> ? [X7] :
                                ( r2_hidden(k4_tarski(X7,X6),X4)
                                & r2_hidden(k4_tarski(X5,X7),X3)
                                & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                     => ! [X5,X6] :
                          ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                        <=> ? [X7] :
                              ( r2_hidden(k4_tarski(X7,X6),X4)
                              & r2_hidden(k4_tarski(X5,X7),X3)
                              & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t51_relset_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',cc1_relset_1)).

fof(f887,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_xboole_0(sK4)
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f836,f156])).

fof(f156,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f91,f71])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f836,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_xboole_0(sK4)
    | ~ spl14_0 ),
    inference(resolution,[],[f827,f201])).

fof(f201,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ r2_hidden(k4_tarski(X18,X19),k5_relat_1(X20,X21))
      | ~ v1_relat_1(X21)
      | ~ v1_relat_1(X20)
      | ~ v1_xboole_0(X21) ) ),
    inference(subsumption_resolution,[],[f196,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',dt_k5_relat_1)).

fof(f196,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ r2_hidden(k4_tarski(X18,X19),k5_relat_1(X20,X21))
      | ~ v1_relat_1(k5_relat_1(X20,X21))
      | ~ v1_relat_1(X21)
      | ~ v1_relat_1(X20)
      | ~ v1_xboole_0(X21) ) ),
    inference(resolution,[],[f102,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t7_boole)).

fof(f102,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK9(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2),sK9(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK8(X0,X1,X2),sK10(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f56,f59,f58,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK9(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK9(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK8(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK10(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',d8_relat_1)).

fof(f827,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f826,f70])).

fof(f826,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f814,f71])).

fof(f814,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl14_0 ),
    inference(superposition,[],[f113,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',redefinition_k4_relset_1)).

fof(f113,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl14_0
  <=> r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f6636,plain,
    ( v1_xboole_0(sK4)
    | ~ spl14_22 ),
    inference(resolution,[],[f170,f136])).

fof(f136,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f87,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK12(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK12(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f13,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK12(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',existence_m1_subset_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t2_subset)).

fof(f170,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK4)
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl14_22
  <=> ! [X1] : ~ r2_hidden(X1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f6558,plain,
    ( ~ spl14_0
    | spl14_25
    | spl14_53 ),
    inference(avatar_contradiction_clause,[],[f6557])).

fof(f6557,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_25
    | ~ spl14_53 ),
    inference(subsumption_resolution,[],[f6554,f906])).

fof(f906,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl14_53 ),
    inference(avatar_component_clause,[],[f905])).

fof(f905,plain,
    ( spl14_53
  <=> ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_53])])).

fof(f6554,plain,
    ( m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl14_0
    | ~ spl14_25 ),
    inference(resolution,[],[f6467,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t1_subset)).

fof(f6467,plain,
    ( r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl14_0
    | ~ spl14_25 ),
    inference(subsumption_resolution,[],[f6417,f155])).

fof(f6417,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl14_0
    | ~ spl14_25 ),
    inference(resolution,[],[f1938,f827])).

fof(f1938,plain,
    ( ! [X85,X86,X84] :
        ( ~ r2_hidden(k4_tarski(X85,X86),k5_relat_1(X84,sK4))
        | ~ v1_relat_1(X84)
        | r2_hidden(sK11(X84,sK4,X85,X86),sK1) )
    | ~ spl14_25 ),
    inference(subsumption_resolution,[],[f1927,f156])).

fof(f1927,plain,
    ( ! [X85,X86,X84] :
        ( ~ v1_relat_1(X84)
        | ~ r2_hidden(k4_tarski(X85,X86),k5_relat_1(X84,sK4))
        | ~ v1_relat_1(sK4)
        | r2_hidden(sK11(X84,sK4,X85,X86),sK1) )
    | ~ spl14_25 ),
    inference(resolution,[],[f384,f360])).

fof(f360,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(k4_tarski(X5,X6),sK4)
        | r2_hidden(X5,sK1) )
    | ~ spl14_25 ),
    inference(resolution,[],[f257,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t106_zfmisc_1)).

fof(f257,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X0,sK4) )
    | ~ spl14_25 ),
    inference(subsumption_resolution,[],[f256,f173])).

fof(f173,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | ~ spl14_25 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl14_25
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_25])])).

fof(f256,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | v1_xboole_0(k2_zfmisc_1(sK1,sK2))
      | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f176,f87])).

fof(f176,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,sK4) ) ),
    inference(resolution,[],[f92,f71])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t4_subset)).

fof(f384,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK11(X1,X0,X2,X3),X3),X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f380,f201])).

fof(f380,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | v1_xboole_0(X0)
      | r2_hidden(k4_tarski(sK11(X1,X0,X2,X3),X3),X0) ) ),
    inference(resolution,[],[f199,f87])).

fof(f199,plain,(
    ! [X12,X10,X13,X11] :
      ( m1_subset_1(k4_tarski(sK11(X12,X13,X10,X11),X11),X13)
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(X12)
      | ~ r2_hidden(k4_tarski(X10,X11),k5_relat_1(X12,X13)) ) ),
    inference(subsumption_resolution,[],[f194,f88])).

fof(f194,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),k5_relat_1(X12,X13))
      | ~ v1_relat_1(k5_relat_1(X12,X13))
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(X12)
      | m1_subset_1(k4_tarski(sK11(X12,X13,X10,X11),X11),X13) ) ),
    inference(resolution,[],[f102,f86])).

fof(f907,plain,
    ( ~ spl14_27
    | ~ spl14_53
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f903,f108,f112,f905,f244])).

fof(f244,plain,
    ( spl14_27
  <=> ~ v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).

fof(f108,plain,
    ( spl14_2
  <=> ! [X7] :
        ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
        | ~ m1_subset_1(X7,sK1)
        | ~ r2_hidden(k4_tarski(sK5,X7),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f903,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f902,f155])).

fof(f902,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f901,f156])).

fof(f901,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f900,f827])).

fof(f900,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl14_2 ),
    inference(duplicate_literal_removal,[],[f899])).

fof(f899,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl14_2 ),
    inference(resolution,[],[f833,f102])).

fof(f833,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK11(sK3,X0,sK5,X1),sK6),sK4)
        | ~ m1_subset_1(sK11(sK3,X0,sK5,X1),sK1)
        | ~ r2_hidden(k4_tarski(sK5,X1),k5_relat_1(sK3,X0))
        | ~ v1_relat_1(k5_relat_1(sK3,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f829,f155])).

fof(f829,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK11(sK3,X0,sK5,X1),sK1)
        | ~ r2_hidden(k4_tarski(sK11(sK3,X0,sK5,X1),sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X1),k5_relat_1(sK3,X0))
        | ~ v1_relat_1(k5_relat_1(sK3,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl14_2 ),
    inference(resolution,[],[f109,f103])).

fof(f103,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f109,plain,
    ( ! [X7] :
        ( ~ r2_hidden(k4_tarski(sK5,X7),sK3)
        | ~ m1_subset_1(X7,sK1)
        | ~ r2_hidden(k4_tarski(X7,sK6),sK4) )
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f803,plain,
    ( ~ spl14_4
    | ~ spl14_6
    | ~ spl14_28 ),
    inference(avatar_contradiction_clause,[],[f802])).

fof(f802,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_28 ),
    inference(subsumption_resolution,[],[f800,f116])).

fof(f116,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl14_4
  <=> r2_hidden(k4_tarski(sK7,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f800,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ spl14_6
    | ~ spl14_28 ),
    inference(resolution,[],[f248,f120])).

fof(f120,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl14_6
  <=> r2_hidden(k4_tarski(sK5,sK7),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ r2_hidden(k4_tarski(X0,sK6),sK4) )
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl14_28
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f253,plain,(
    spl14_27 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl14_27 ),
    inference(subsumption_resolution,[],[f251,f155])).

fof(f251,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl14_27 ),
    inference(subsumption_resolution,[],[f250,f156])).

fof(f250,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl14_27 ),
    inference(resolution,[],[f245,f88])).

fof(f245,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl14_27 ),
    inference(avatar_component_clause,[],[f244])).

fof(f249,plain,
    ( ~ spl14_27
    | spl14_28
    | spl14_1 ),
    inference(avatar_split_clause,[],[f242,f105,f247,f244])).

fof(f105,plain,
    ( spl14_1
  <=> ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ v1_relat_1(k5_relat_1(sK3,sK4)) )
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f241,f155])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ v1_relat_1(k5_relat_1(sK3,sK4))
        | ~ v1_relat_1(sK3) )
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f240,f156])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ v1_relat_1(k5_relat_1(sK3,sK4))
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(sK3) )
    | ~ spl14_1 ),
    inference(resolution,[],[f185,f101])).

fof(f101,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f185,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f184,f70])).

fof(f184,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f183,f71])).

fof(f183,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl14_1 ),
    inference(superposition,[],[f106,f97])).

fof(f106,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f174,plain,
    ( spl14_22
    | ~ spl14_25 ),
    inference(avatar_split_clause,[],[f159,f172,f169])).

fof(f159,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,sK4) ) ),
    inference(resolution,[],[f93,f71])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t5_subset)).

fof(f121,plain,
    ( spl14_0
    | spl14_6 ),
    inference(avatar_split_clause,[],[f73,f119,f112])).

fof(f73,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f117,plain,
    ( spl14_0
    | spl14_4 ),
    inference(avatar_split_clause,[],[f74,f115,f112])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),sK4)
    | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f110,plain,
    ( ~ spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f75,f108,f105])).

fof(f75,plain,(
    ! [X7] :
      ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
      | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
      | ~ m1_subset_1(X7,sK1)
      | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
