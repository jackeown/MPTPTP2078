%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 991 expanded)
%              Number of leaves         :   15 ( 346 expanded)
%              Depth                    :   33
%              Number of atoms          :  533 (8114 expanded)
%              Number of equality atoms :   15 ( 136 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(subsumption_resolution,[],[f303,f62])).

fof(f62,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
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
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f21,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
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
                    | ~ m1_subset_1(X7,sK1) )
                | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)) )
              & ( ? [X8] :
                    ( r2_hidden(k4_tarski(X8,X6),X4)
                    & r2_hidden(k4_tarski(X5,X8),sK3)
                    & m1_subset_1(X8,sK1) )
                | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X4] :
        ( ? [X6,X5] :
            ( ( ! [X7] :
                  ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                  | ~ r2_hidden(k4_tarski(X5,X7),sK3)
                  | ~ m1_subset_1(X7,sK1) )
              | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)) )
            & ( ? [X8] :
                  ( r2_hidden(k4_tarski(X8,X6),X4)
                  & r2_hidden(k4_tarski(X5,X8),sK3)
                  & m1_subset_1(X8,sK1) )
              | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)) ) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) )
   => ( ? [X6,X5] :
          ( ( ! [X7] :
                ( ~ r2_hidden(k4_tarski(X7,X6),sK4)
                | ~ r2_hidden(k4_tarski(X5,X7),sK3)
                | ~ m1_subset_1(X7,sK1) )
            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
          & ( ? [X8] :
                ( r2_hidden(k4_tarski(X8,X6),sK4)
                & r2_hidden(k4_tarski(X5,X8),sK3)
                & m1_subset_1(X8,sK1) )
            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X6,X5] :
        ( ( ! [X7] :
              ( ~ r2_hidden(k4_tarski(X7,X6),sK4)
              | ~ r2_hidden(k4_tarski(X5,X7),sK3)
              | ~ m1_subset_1(X7,sK1) )
          | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
        & ( ? [X8] :
              ( r2_hidden(k4_tarski(X8,X6),sK4)
              & r2_hidden(k4_tarski(X5,X8),sK3)
              & m1_subset_1(X8,sK1) )
          | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) )
   => ( ( ! [X7] :
            ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
            | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
            | ~ m1_subset_1(X7,sK1) )
        | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
      & ( ? [X8] :
            ( r2_hidden(k4_tarski(X8,sK6),sK4)
            & r2_hidden(k4_tarski(sK5,X8),sK3)
            & m1_subset_1(X8,sK1) )
        | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X8] :
        ( r2_hidden(k4_tarski(X8,sK6),sK4)
        & r2_hidden(k4_tarski(sK5,X8),sK3)
        & m1_subset_1(X8,sK1) )
   => ( r2_hidden(k4_tarski(sK7,sK6),sK4)
      & r2_hidden(k4_tarski(sK5,sK7),sK3)
      & m1_subset_1(sK7,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
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
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
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
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6] :
              ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
            <~> ? [X7] :
                  ( r2_hidden(k4_tarski(X7,X6),X4)
                  & r2_hidden(k4_tarski(X5,X7),X3)
                  & m1_subset_1(X7,X1) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
           => ! [X5,X6] :
                ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
              <=> ? [X7] :
                    ( r2_hidden(k4_tarski(X7,X6),X4)
                    & r2_hidden(k4_tarski(X5,X7),X3)
                    & m1_subset_1(X7,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f303,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f302,f63])).

fof(f63,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f302,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f301,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f301,plain,(
    ~ v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f300,f288])).

fof(f288,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | r2_hidden(k4_tarski(sK7,sK6),sK4) ),
    inference(resolution,[],[f286,f86])).

fof(f86,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | r2_hidden(k4_tarski(sK7,sK6),sK4) ),
    inference(subsumption_resolution,[],[f85,f35])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f80,f36])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f39,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f39,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | r2_hidden(k4_tarski(sK7,sK6),sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f286,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f285,f63])).

fof(f285,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f281,f140])).

fof(f140,plain,(
    ! [X24,X23,X22] :
      ( r2_hidden(sK11(sK3,X24,X22,X23),sK1)
      | ~ v1_relat_1(k5_relat_1(sK3,X24))
      | ~ v1_relat_1(X24)
      | ~ r2_hidden(k4_tarski(X22,X23),k5_relat_1(sK3,X24)) ) ),
    inference(subsumption_resolution,[],[f126,f62])).

fof(f126,plain,(
    ! [X24,X23,X22] :
      ( ~ r2_hidden(k4_tarski(X22,X23),k5_relat_1(sK3,X24))
      | ~ v1_relat_1(k5_relat_1(sK3,X24))
      | ~ v1_relat_1(X24)
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK11(sK3,X24,X22,X23),sK1) ) ),
    inference(resolution,[],[f57,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK3)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f48,f35])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f57,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f28,f31,f30,f29])).

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK9(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK8(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK10(X0,X1,X2),sK9(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),sK10(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f281,plain,
    ( ~ r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f248,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f248,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f247,f62])).

fof(f247,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f246,f63])).

fof(f246,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f204,f56])).

fof(f56,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f204,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(sK11(sK3,X1,sK5,X2),sK6),sK4)
      | ~ v1_relat_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK11(sK3,X1,sK5,X2),sK1)
      | ~ r2_hidden(k4_tarski(sK5,X2),k5_relat_1(sK3,X1))
      | ~ v1_relat_1(k5_relat_1(sK3,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f202,f62])).

fof(f202,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(sK11(sK3,X1,sK5,X2),sK6),sK4)
      | ~ v1_relat_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK11(sK3,X1,sK5,X2),sK1)
      | ~ r2_hidden(k4_tarski(sK5,X2),k5_relat_1(sK3,X1))
      | ~ v1_relat_1(k5_relat_1(sK3,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f199,f57])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ r2_hidden(k4_tarski(X0,sK6),sK4)
      | ~ v1_relat_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f198,f62])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
      | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ v1_relat_1(k5_relat_1(sK3,sK4))
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f197,f63])).

fof(f197,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
      | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ v1_relat_1(k5_relat_1(sK3,sK4))
      | ~ v1_relat_1(sK4)
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
      | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ v1_relat_1(k5_relat_1(sK3,sK4))
      | ~ v1_relat_1(sK4)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(condensation,[],[f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
      | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ v1_relat_1(k5_relat_1(sK3,sK4))
      | ~ v1_relat_1(sK4)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(k4_tarski(sK5,X1),sK3)
      | ~ m1_subset_1(X1,sK1)
      | ~ r2_hidden(k4_tarski(X1,sK6),sK4) ) ),
    inference(resolution,[],[f55,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
      | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ m1_subset_1(X0,sK1)
      | ~ r2_hidden(k4_tarski(X0,sK6),sK4) ) ),
    inference(subsumption_resolution,[],[f83,f35])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
      | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ m1_subset_1(X0,sK1)
      | ~ r2_hidden(k4_tarski(X0,sK6),sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f79,f36])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
      | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
      | ~ m1_subset_1(X0,sK1)
      | ~ r2_hidden(k4_tarski(X0,sK6),sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f40,f54])).

fof(f40,plain,(
    ! [X7] :
      ( ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
      | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
      | ~ m1_subset_1(X7,sK1)
      | ~ r2_hidden(k4_tarski(X7,sK6),sK4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f300,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK7,sK6),sK4) ),
    inference(subsumption_resolution,[],[f299,f225])).

fof(f225,plain,(
    m1_subset_1(sK7,sK1) ),
    inference(subsumption_resolution,[],[f224,f62])).

fof(f224,plain,
    ( m1_subset_1(sK7,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f223,f63])).

fof(f223,plain,
    ( m1_subset_1(sK7,sK1)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f222,f49])).

fof(f222,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1) ),
    inference(subsumption_resolution,[],[f221,f90])).

fof(f90,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1) ),
    inference(subsumption_resolution,[],[f89,f35])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f82,f36])).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f37,f54])).

fof(f37,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | m1_subset_1(sK7,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f221,plain,
    ( m1_subset_1(sK7,sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f220,f63])).

fof(f220,plain,
    ( m1_subset_1(sK7,sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( m1_subset_1(sK7,sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f216,f140])).

fof(f216,plain,
    ( ~ r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)
    | m1_subset_1(sK7,sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f215,f47])).

fof(f215,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1) ),
    inference(subsumption_resolution,[],[f214,f90])).

fof(f214,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1) ),
    inference(subsumption_resolution,[],[f213,f62])).

fof(f213,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f212,f63])).

fof(f212,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | m1_subset_1(sK7,sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f135,f56])).

fof(f135,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK11(sK3,X3,sK5,X2),sK6),sK4)
      | ~ v1_relat_1(k5_relat_1(sK3,X3))
      | ~ v1_relat_1(X3)
      | ~ m1_subset_1(sK11(sK3,X3,sK5,X2),sK1)
      | ~ r2_hidden(k4_tarski(sK5,X2),k5_relat_1(sK3,X3))
      | m1_subset_1(sK7,sK1) ) ),
    inference(subsumption_resolution,[],[f121,f62])).

fof(f121,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK5,X2),k5_relat_1(sK3,X3))
      | ~ v1_relat_1(k5_relat_1(sK3,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK11(sK3,X3,sK5,X2),sK1)
      | ~ r2_hidden(k4_tarski(sK11(sK3,X3,sK5,X2),sK6),sK4)
      | m1_subset_1(sK7,sK1) ) ),
    inference(resolution,[],[f57,f60])).

fof(f60,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(sK5,X2),sK3)
      | ~ m1_subset_1(X2,sK1)
      | ~ r2_hidden(k4_tarski(X2,sK6),sK4)
      | m1_subset_1(sK7,sK1) ) ),
    inference(resolution,[],[f40,f37])).

fof(f299,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ m1_subset_1(sK7,sK1) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK7,sK1) ),
    inference(resolution,[],[f287,f199])).

fof(f287,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f286,f88])).

fof(f88,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | r2_hidden(k4_tarski(sK5,sK7),sK3) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f87,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | r2_hidden(k4_tarski(sK5,sK7),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f81,f36])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | r2_hidden(k4_tarski(sK5,sK7),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f38,f54])).

fof(f38,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | r2_hidden(k4_tarski(sK5,sK7),sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:48:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (11330)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (11336)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (11341)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (11325)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (11337)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (11338)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (11343)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (11326)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (11327)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (11329)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (11333)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (11323)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (11328)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (11340)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (11332)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (11336)Refutation not found, incomplete strategy% (11336)------------------------------
% 0.20/0.49  % (11336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11336)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (11336)Memory used [KB]: 1663
% 0.20/0.49  % (11336)Time elapsed: 0.086 s
% 0.20/0.49  % (11336)------------------------------
% 0.20/0.49  % (11336)------------------------------
% 0.20/0.49  % (11335)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (11331)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (11341)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f303,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f50,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    (((! [X7] : (~r2_hidden(k4_tarski(X7,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) & ((r2_hidden(k4_tarski(sK7,sK6),sK4) & r2_hidden(k4_tarski(sK5,sK7),sK3) & m1_subset_1(sK7,sK1)) | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f21,f25,f24,f23,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (? [X4] : (? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X4] : (? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) => (? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),sK4) | ~r2_hidden(k4_tarski(X5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),sK4) & r2_hidden(k4_tarski(X5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),sK4) | ~r2_hidden(k4_tarski(X5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),sK4) & r2_hidden(k4_tarski(X5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)))) => ((! [X7] : (~r2_hidden(k4_tarski(X7,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) & (? [X8] : (r2_hidden(k4_tarski(X8,sK6),sK4) & r2_hidden(k4_tarski(sK5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X8] : (r2_hidden(k4_tarski(X8,sK6),sK4) & r2_hidden(k4_tarski(sK5,X8),sK3) & m1_subset_1(X8,sK1)) => (r2_hidden(k4_tarski(sK7,sK6),sK4) & r2_hidden(k4_tarski(sK5,sK7),sK3) & m1_subset_1(sK7,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(rectify,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <~> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1)))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.50  fof(f9,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f8])).
% 0.20/0.50  fof(f8,conjecture,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relset_1)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    ~v1_relat_1(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f302,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    v1_relat_1(sK4)),
% 0.20/0.50    inference(resolution,[],[f50,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f301,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(subsumption_resolution,[],[f300,f288])).
% 0.20/0.50  fof(f288,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | r2_hidden(k4_tarski(sK7,sK6),sK4)),
% 0.20/0.50    inference(resolution,[],[f286,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | r2_hidden(k4_tarski(sK7,sK6),sK4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f85,f35])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | r2_hidden(k4_tarski(sK7,sK6),sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f80,f36])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | r2_hidden(k4_tarski(sK7,sK6),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(superposition,[],[f39,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) | r2_hidden(k4_tarski(sK7,sK6),sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(subsumption_resolution,[],[f285,f63])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f282])).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(resolution,[],[f281,f140])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ( ! [X24,X23,X22] : (r2_hidden(sK11(sK3,X24,X22,X23),sK1) | ~v1_relat_1(k5_relat_1(sK3,X24)) | ~v1_relat_1(X24) | ~r2_hidden(k4_tarski(X22,X23),k5_relat_1(sK3,X24))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f126,f62])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X24,X23,X22] : (~r2_hidden(k4_tarski(X22,X23),k5_relat_1(sK3,X24)) | ~v1_relat_1(k5_relat_1(sK3,X24)) | ~v1_relat_1(X24) | ~v1_relat_1(sK3) | r2_hidden(sK11(sK3,X24,X22,X23),sK1)) )),
% 0.20/0.50    inference(resolution,[],[f57,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK3) | r2_hidden(X0,sK1)) )),
% 0.20/0.50    inference(resolution,[],[f52,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3)) )),
% 0.20/0.50    inference(resolution,[],[f48,f35])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.50    inference(flattening,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK9(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2),sK9(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),sK10(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f28,f31,f30,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK9(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK9(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK9(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK10(X0,X1,X2),sK9(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),sK10(X0,X1,X2)),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(rectify,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    ~r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(resolution,[],[f248,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(subsumption_resolution,[],[f247,f62])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f246,f63])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f245])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f204,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~r2_hidden(k4_tarski(sK11(sK3,X1,sK5,X2),sK6),sK4) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK11(sK3,X1,sK5,X2),sK1) | ~r2_hidden(k4_tarski(sK5,X2),k5_relat_1(sK3,X1)) | ~v1_relat_1(k5_relat_1(sK3,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f202,f62])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~r2_hidden(k4_tarski(sK11(sK3,X1,sK5,X2),sK6),sK4) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK11(sK3,X1,sK5,X2),sK1) | ~r2_hidden(k4_tarski(sK5,X2),k5_relat_1(sK3,X1)) | ~v1_relat_1(k5_relat_1(sK3,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(sK3)) )),
% 0.20/0.50    inference(resolution,[],[f199,f57])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(sK5,X0),sK3) | ~r2_hidden(k4_tarski(X0,sK6),sK4) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(X0,sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f198,f62])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK3) | ~m1_subset_1(X0,sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f197,f63])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | ~m1_subset_1(X0,sK1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f196])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~m1_subset_1(X0,sK1)) )),
% 0.20/0.50    inference(condensation,[],[f181])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(sK5,X1),sK3) | ~m1_subset_1(X1,sK1) | ~r2_hidden(k4_tarski(X1,sK6),sK4)) )),
% 0.20/0.50    inference(resolution,[],[f55,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~m1_subset_1(X0,sK1) | ~r2_hidden(k4_tarski(X0,sK6),sK4)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f83,f35])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~m1_subset_1(X0,sK1) | ~r2_hidden(k4_tarski(X0,sK6),sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f79,f36])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~m1_subset_1(X0,sK1) | ~r2_hidden(k4_tarski(X0,sK6),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.50    inference(superposition,[],[f40,f54])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X7] : (~r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) | ~r2_hidden(k4_tarski(sK5,X7),sK3) | ~m1_subset_1(X7,sK1) | ~r2_hidden(k4_tarski(X7,sK6),sK4)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~r2_hidden(k4_tarski(sK7,sK6),sK4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f299,f225])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    m1_subset_1(sK7,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f224,f62])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    m1_subset_1(sK7,sK1) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f223,f63])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    m1_subset_1(sK7,sK1) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f222,f49])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f221,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f89,f35])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f82,f36])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(superposition,[],[f37,f54])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) | m1_subset_1(sK7,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    m1_subset_1(sK7,sK1) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(subsumption_resolution,[],[f220,f63])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    m1_subset_1(sK7,sK1) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f217])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    m1_subset_1(sK7,sK1) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(resolution,[],[f216,f140])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    ~r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1) | m1_subset_1(sK7,sK1) | ~v1_relat_1(k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(resolution,[],[f215,f47])).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f214,f90])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f213,f62])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f212,f63])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | m1_subset_1(sK7,sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f135,f56])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK11(sK3,X3,sK5,X2),sK6),sK4) | ~v1_relat_1(k5_relat_1(sK3,X3)) | ~v1_relat_1(X3) | ~m1_subset_1(sK11(sK3,X3,sK5,X2),sK1) | ~r2_hidden(k4_tarski(sK5,X2),k5_relat_1(sK3,X3)) | m1_subset_1(sK7,sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f121,f62])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK5,X2),k5_relat_1(sK3,X3)) | ~v1_relat_1(k5_relat_1(sK3,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(sK3) | ~m1_subset_1(sK11(sK3,X3,sK5,X2),sK1) | ~r2_hidden(k4_tarski(sK11(sK3,X3,sK5,X2),sK6),sK4) | m1_subset_1(sK7,sK1)) )),
% 0.20/0.50    inference(resolution,[],[f57,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(k4_tarski(sK5,X2),sK3) | ~m1_subset_1(X2,sK1) | ~r2_hidden(k4_tarski(X2,sK6),sK4) | m1_subset_1(sK7,sK1)) )),
% 0.20/0.50    inference(resolution,[],[f40,f37])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~r2_hidden(k4_tarski(sK7,sK6),sK4) | ~m1_subset_1(sK7,sK1)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f294])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~r2_hidden(k4_tarski(sK7,sK6),sK4) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK7,sK1)),
% 0.20/0.50    inference(resolution,[],[f287,f199])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK7),sK3) | ~v1_relat_1(k5_relat_1(sK3,sK4))),
% 0.20/0.50    inference(resolution,[],[f286,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | r2_hidden(k4_tarski(sK5,sK7),sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f87,f35])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | r2_hidden(k4_tarski(sK5,sK7),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f81,f36])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | r2_hidden(k4_tarski(sK5,sK7),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(superposition,[],[f38,f54])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) | r2_hidden(k4_tarski(sK5,sK7),sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (11341)------------------------------
% 0.20/0.50  % (11341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (11341)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (11341)Memory used [KB]: 1918
% 0.20/0.50  % (11341)Time elapsed: 0.076 s
% 0.20/0.50  % (11341)------------------------------
% 0.20/0.50  % (11341)------------------------------
% 0.20/0.50  % (11342)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (11322)Success in time 0.143 s
%------------------------------------------------------------------------------
