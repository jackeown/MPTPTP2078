%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:48 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  148 (2337 expanded)
%              Number of clauses        :   89 ( 409 expanded)
%              Number of leaves         :   16 ( 976 expanded)
%              Depth                    :   29
%              Number of atoms          :  684 (19547 expanded)
%              Number of equality atoms :  177 ( 722 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    ! [X4,X3,X0,X1,X2] :
      ( ( k6_funct_2(X0,X1,X2,X3) = X4
      <=> sP0(X2,X1,X0,X3,X4) )
      | ~ sP1(X4,X3,X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X4,X3,X0,X1,X2] :
      ( ( ( k6_funct_2(X0,X1,X2,X3) = X4
          | ~ sP0(X2,X1,X0,X3,X4) )
        & ( sP0(X2,X1,X0,X3,X4)
          | k6_funct_2(X0,X1,X2,X3) != X4 ) )
      | ~ sP1(X4,X3,X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( k6_funct_2(X2,X3,X4,X1) = X0
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | k6_funct_2(X2,X3,X4,X1) != X0 ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f21])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | k6_funct_2(X2,X3,X4,X1) != X0
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X4,X2,X3,X1] :
      ( sP0(X4,X3,X2,X1,k6_funct_2(X2,X3,X4,X1))
      | ~ sP1(k6_funct_2(X2,X3,X4,X1),X1,X2,X3,X4) ) ),
    inference(equality_resolution,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
                     => ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(X0))
                           => ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X2,X1,X0,X3,X4] :
      ( sP0(X2,X1,X0,X3,X4)
    <=> ! [X5] :
          ( ( r2_hidden(X5,X4)
          <=> ? [X6] :
                ( k8_relset_1(X0,X1,X2,X6) = X5
                & r2_hidden(X6,X3)
                & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
          | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X4,X3,X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f9,f19,f18])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X4,X3,X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                     => ( r1_tarski(X3,X4)
                       => r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                       => ( r1_tarski(X3,X4)
                         => r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
          & r1_tarski(X3,X4)
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
     => ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,sK10))
        & r1_tarski(X3,sK10)
        & m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
              & r1_tarski(X3,X4)
              & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
     => ( ? [X4] :
            ( ~ r1_tarski(k6_funct_2(X0,X1,X2,sK9),k6_funct_2(X0,X1,X2,X4))
            & r1_tarski(sK9,X4)
            & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
        & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                  & r1_tarski(X3,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r1_tarski(k6_funct_2(X0,X1,sK8,X3),k6_funct_2(X0,X1,sK8,X4))
                & r1_tarski(X3,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK8,X0,X1)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_tarski(k6_funct_2(X0,sK7,X2,X3),k6_funct_2(X0,sK7,X2,X4))
                    & r1_tarski(X3,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK7))) )
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK7))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK7)))
            & v1_funct_2(X2,X0,sK7)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                        & r1_tarski(X3,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k6_funct_2(sK6,X1,X2,X3),k6_funct_2(sK6,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
              & v1_funct_2(X2,sK6,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))
    & r1_tarski(sK9,sK10)
    & m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK8,sK6,sK7)
    & v1_funct_1(sK8)
    & ~ v1_xboole_0(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f17,f38,f37,f36,f35,f34])).

fof(f61,plain,(
    v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X2,X1,X0,X3,X4] :
      ( ( sP0(X2,X1,X0,X3,X4)
        | ? [X5] :
            ( ( ! [X6] :
                  ( k8_relset_1(X0,X1,X2,X6) != X5
                  | ~ r2_hidden(X6,X3)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
              | ~ r2_hidden(X5,X4) )
            & ( ? [X6] :
                  ( k8_relset_1(X0,X1,X2,X6) = X5
                  & r2_hidden(X6,X3)
                  & m1_subset_1(X6,k1_zfmisc_1(X1)) )
              | r2_hidden(X5,X4) )
            & m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
      & ( ! [X5] :
            ( ( ( r2_hidden(X5,X4)
                | ! [X6] :
                    ( k8_relset_1(X0,X1,X2,X6) != X5
                    | ~ r2_hidden(X6,X3)
                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
              & ( ? [X6] :
                    ( k8_relset_1(X0,X1,X2,X6) = X5
                    & r2_hidden(X6,X3)
                    & m1_subset_1(X6,k1_zfmisc_1(X1)) )
                | ~ r2_hidden(X5,X4) ) )
            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) )
        | ~ sP0(X2,X1,X0,X3,X4) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X2,X1,X0,X3,X4] :
      ( ( sP0(X2,X1,X0,X3,X4)
        | ? [X5] :
            ( ( ! [X6] :
                  ( k8_relset_1(X0,X1,X2,X6) != X5
                  | ~ r2_hidden(X6,X3)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
              | ~ r2_hidden(X5,X4) )
            & ( ? [X6] :
                  ( k8_relset_1(X0,X1,X2,X6) = X5
                  & r2_hidden(X6,X3)
                  & m1_subset_1(X6,k1_zfmisc_1(X1)) )
              | r2_hidden(X5,X4) )
            & m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
      & ( ! [X5] :
            ( ( ( r2_hidden(X5,X4)
                | ! [X6] :
                    ( k8_relset_1(X0,X1,X2,X6) != X5
                    | ~ r2_hidden(X6,X3)
                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
              & ( ? [X6] :
                    ( k8_relset_1(X0,X1,X2,X6) = X5
                    & r2_hidden(X6,X3)
                    & m1_subset_1(X6,k1_zfmisc_1(X1)) )
                | ~ r2_hidden(X5,X4) ) )
            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) )
        | ~ sP0(X2,X1,X0,X3,X4) ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ! [X6] :
                  ( k8_relset_1(X2,X1,X0,X6) != X5
                  | ~ r2_hidden(X6,X3)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
              | ~ r2_hidden(X5,X4) )
            & ( ? [X7] :
                  ( k8_relset_1(X2,X1,X0,X7) = X5
                  & r2_hidden(X7,X3)
                  & m1_subset_1(X7,k1_zfmisc_1(X1)) )
              | r2_hidden(X5,X4) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) ) )
      & ( ! [X8] :
            ( ( ( r2_hidden(X8,X4)
                | ! [X9] :
                    ( k8_relset_1(X2,X1,X0,X9) != X8
                    | ~ r2_hidden(X9,X3)
                    | ~ m1_subset_1(X9,k1_zfmisc_1(X1)) ) )
              & ( ? [X10] :
                    ( k8_relset_1(X2,X1,X0,X10) = X8
                    & r2_hidden(X10,X3)
                    & m1_subset_1(X10,k1_zfmisc_1(X1)) )
                | ~ r2_hidden(X8,X4) ) )
            | ~ m1_subset_1(X8,k1_zfmisc_1(X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X8,X3,X2,X1,X0] :
      ( ? [X10] :
          ( k8_relset_1(X2,X1,X0,X10) = X8
          & r2_hidden(X10,X3)
          & m1_subset_1(X10,k1_zfmisc_1(X1)) )
     => ( k8_relset_1(X2,X1,X0,sK4(X0,X1,X2,X3,X8)) = X8
        & r2_hidden(sK4(X0,X1,X2,X3,X8),X3)
        & m1_subset_1(sK4(X0,X1,X2,X3,X8),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( k8_relset_1(X2,X1,X0,X7) = X5
          & r2_hidden(X7,X3)
          & m1_subset_1(X7,k1_zfmisc_1(X1)) )
     => ( k8_relset_1(X2,X1,X0,sK3(X0,X1,X2,X3,X4)) = X5
        & r2_hidden(sK3(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK3(X0,X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ! [X6] :
                ( k8_relset_1(X2,X1,X0,X6) != X5
                | ~ r2_hidden(X6,X3)
                | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
            | ~ r2_hidden(X5,X4) )
          & ( ? [X7] :
                ( k8_relset_1(X2,X1,X0,X7) = X5
                & r2_hidden(X7,X3)
                & m1_subset_1(X7,k1_zfmisc_1(X1)) )
            | r2_hidden(X5,X4) )
          & m1_subset_1(X5,k1_zfmisc_1(X2)) )
     => ( ( ! [X6] :
              ( k8_relset_1(X2,X1,X0,X6) != sK2(X0,X1,X2,X3,X4)
              | ~ r2_hidden(X6,X3)
              | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
        & ( ? [X7] :
              ( k8_relset_1(X2,X1,X0,X7) = sK2(X0,X1,X2,X3,X4)
              & r2_hidden(X7,X3)
              & m1_subset_1(X7,k1_zfmisc_1(X1)) )
          | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
        & m1_subset_1(sK2(X0,X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ! [X6] :
                ( k8_relset_1(X2,X1,X0,X6) != sK2(X0,X1,X2,X3,X4)
                | ~ r2_hidden(X6,X3)
                | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
          & ( ( k8_relset_1(X2,X1,X0,sK3(X0,X1,X2,X3,X4)) = sK2(X0,X1,X2,X3,X4)
              & r2_hidden(sK3(X0,X1,X2,X3,X4),X3)
              & m1_subset_1(sK3(X0,X1,X2,X3,X4),k1_zfmisc_1(X1)) )
            | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
          & m1_subset_1(sK2(X0,X1,X2,X3,X4),k1_zfmisc_1(X2)) ) )
      & ( ! [X8] :
            ( ( ( r2_hidden(X8,X4)
                | ! [X9] :
                    ( k8_relset_1(X2,X1,X0,X9) != X8
                    | ~ r2_hidden(X9,X3)
                    | ~ m1_subset_1(X9,k1_zfmisc_1(X1)) ) )
              & ( ( k8_relset_1(X2,X1,X0,sK4(X0,X1,X2,X3,X8)) = X8
                  & r2_hidden(sK4(X0,X1,X2,X3,X8),X3)
                  & m1_subset_1(sK4(X0,X1,X2,X3,X8),k1_zfmisc_1(X1)) )
                | ~ r2_hidden(X8,X4) ) )
            | ~ m1_subset_1(X8,k1_zfmisc_1(X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f43,plain,(
    ! [X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X2,X3,X8),X3)
      | ~ r2_hidden(X8,X4)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    r1_tarski(sK9,sK10) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ! [X4,X2,X0,X8,X3,X1] :
      ( k8_relset_1(X2,X1,X0,sK4(X0,X1,X2,X3,X8)) = X8
      | ~ r2_hidden(X8,X4)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ~ r1_tarski(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) ),
    inference(cnf_transformation,[],[f39])).

fof(f45,plain,(
    ! [X4,X2,X0,X8,X3,X1,X9] :
      ( r2_hidden(X8,X4)
      | k8_relset_1(X2,X1,X0,X9) != X8
      | ~ r2_hidden(X9,X3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1,X9] :
      ( r2_hidden(k8_relset_1(X2,X1,X0,X9),X4)
      | ~ r2_hidden(X9,X3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k8_relset_1(X2,X1,X0,X9),k1_zfmisc_1(X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(equality_resolution,[],[f45])).

fof(f42,plain,(
    ! [X4,X2,X0,X8,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3,X8),k1_zfmisc_1(X1))
      | ~ r2_hidden(X8,X4)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(sK7))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( ~ sP1(k6_funct_2(X0,X1,X2,X3),X3,X0,X1,X2)
    | sP0(X2,X1,X0,X3,k6_funct_2(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_366,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X4)
    | sK8 != X4
    | sK7 != X3
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_367,plain,
    ( sP1(X0,X1,sK6,sK7,sK8)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | ~ v1_funct_1(sK8) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_371,plain,
    ( sP1(X0,X1,sK6,sK7,sK8)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_26,c_25,c_24,c_22])).

cnf(c_430,plain,
    ( sP0(X0,X1,X2,X3,k6_funct_2(X2,X1,X0,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(sK6)))
    | X4 != X3
    | k6_funct_2(X2,X1,X0,X3) != X5
    | sK8 != X0
    | sK7 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_371])).

cnf(c_431,plain,
    ( sP0(sK8,sK7,sK6,X0,k6_funct_2(sK6,sK7,sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | ~ m1_subset_1(k6_funct_2(sK6,sK7,sK8,X0),k1_zfmisc_1(k1_zfmisc_1(sK6))) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | m1_subset_1(k6_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | m1_subset_1(k6_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | sK8 != X0
    | sK7 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | m1_subset_1(k6_funct_2(sK6,sK7,sK8,X0),k1_zfmisc_1(k1_zfmisc_1(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | ~ v1_funct_1(sK8) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | m1_subset_1(k6_funct_2(sK6,sK7,sK8,X0),k1_zfmisc_1(k1_zfmisc_1(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_26,c_25,c_24,c_22])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | sP0(sK8,sK7,sK6,X0,k6_funct_2(sK6,sK7,sK8,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_26,c_25,c_24,c_22,c_388])).

cnf(c_436,plain,
    ( sP0(sK8,sK7,sK6,X0,k6_funct_2(sK6,sK7,sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) ),
    inference(renaming,[status(thm)],[c_435])).

cnf(c_2537,plain,
    ( sP0(sK8,sK7,sK6,X0,k6_funct_2(sK6,sK7,sK8,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_hidden(X5,X4)
    | r2_hidden(sK4(X0,X1,X2,X3,X5),X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2551,plain,
    ( sP0(X0,X1,X2,X3,X4) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(X5,X4) != iProver_top
    | r2_hidden(sK4(X0,X1,X2,X3,X5),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3886,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK6)) != iProver_top
    | r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0)) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK6,X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_2551])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | ~ r2_hidden(X0,X3)
    | r2_hidden(sK4(X4,X5,X1,X6,X0),X6)
    | X2 != X6
    | k6_funct_2(sK6,sK7,sK8,X2) != X3
    | sK8 != X4
    | sK7 != X5
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_436])).

cnf(c_1012,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK6))
    | ~ r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0))
    | r2_hidden(sK4(sK8,sK7,sK6,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1011])).

cnf(c_1013,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK6)) != iProver_top
    | r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0)) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK6,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_2539,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | m1_subset_1(k6_funct_2(sK6,sK7,sK8,X0),k1_zfmisc_1(k1_zfmisc_1(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2545,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2970,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK6)) = iProver_top
    | r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2539,c_2545])).

cnf(c_4095,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0)) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK6,X0,X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_1013,c_2970])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK9,sK10) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2543,plain,
    ( r1_tarski(sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2547,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3059,plain,
    ( r2_hidden(X0,sK10) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_2547])).

cnf(c_4106,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | r2_hidden(X0,k6_funct_2(sK6,sK7,sK8,sK9)) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK6,sK9,X0),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4095,c_3059])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4151,plain,
    ( r2_hidden(X0,k6_funct_2(sK6,sK7,sK8,sK9)) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK6,sK9,X0),sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4106,c_32])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2548,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK5(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_hidden(X5,X4)
    | k8_relset_1(X2,X1,X0,sK4(X0,X1,X2,X3,X5)) = X5 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2552,plain,
    ( k8_relset_1(X0,X1,X2,sK4(X2,X1,X0,X3,X4)) = X4
    | sP0(X2,X1,X0,X3,X5) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X4,X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4270,plain,
    ( k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,X0,X1)) = X1
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK6)) != iProver_top
    | r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_2552])).

cnf(c_1029,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | ~ r2_hidden(X0,X3)
    | X2 != X4
    | k8_relset_1(X1,X5,X6,sK4(X6,X5,X1,X4,X0)) = X0
    | k6_funct_2(sK6,sK7,sK8,X2) != X3
    | sK8 != X6
    | sK7 != X5
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_436])).

cnf(c_1030,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK6))
    | ~ r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0))
    | k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_1029])).

cnf(c_1031,plain,
    ( k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,X0,X1)) = X1
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK6)) != iProver_top
    | r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_4961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,X0,X1)) = X1
    | r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4270,c_1031,c_2970])).

cnf(c_4962,plain,
    ( k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,X0,X1)) = X1
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top
    | r2_hidden(X1,k6_funct_2(sK6,sK7,sK8,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4961])).

cnf(c_4973,plain,
    ( k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,X0,sK5(k6_funct_2(sK6,sK7,sK8,X0),X1))) = sK5(k6_funct_2(sK6,sK7,sK8,X0),X1)
    | r1_tarski(k6_funct_2(sK6,sK7,sK8,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_4962])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2544,plain,
    ( r1_tarski(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8921,plain,
    ( k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)))) = sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))
    | m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4973,c_2544])).

cnf(c_321,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | k6_funct_2(sK6,sK7,sK8,sK10) != X1
    | k6_funct_2(sK6,sK7,sK8,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_322,plain,
    ( r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_2726,plain,
    ( m1_subset_1(k6_funct_2(sK6,sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(sK6)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_2732,plain,
    ( sP0(sK8,sK7,sK6,sK9,k6_funct_2(sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_2824,plain,
    ( ~ m1_subset_1(k6_funct_2(sK6,sK7,sK8,sK9),k1_zfmisc_1(X0))
    | m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),X0)
    | ~ r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3028,plain,
    ( ~ m1_subset_1(k6_funct_2(sK6,sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(sK6)))
    | m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6))
    | ~ r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_2824])).

cnf(c_2804,plain,
    ( ~ sP0(X0,X1,X2,X3,k6_funct_2(sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(X2))
    | ~ r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9))
    | k8_relset_1(X2,X1,X0,sK4(X0,X1,X2,X3,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)))) = sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3134,plain,
    ( ~ sP0(X0,X1,sK6,X2,k6_funct_2(sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6))
    | ~ r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9))
    | k8_relset_1(sK6,X1,X0,sK4(X0,X1,sK6,X2,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)))) = sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) ),
    inference(instantiation,[status(thm)],[c_2804])).

cnf(c_3734,plain,
    ( ~ sP0(sK8,sK7,sK6,sK9,k6_funct_2(sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6))
    | ~ r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9))
    | k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)))) = sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_9008,plain,
    ( k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)))) = sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8921,c_21,c_322,c_2726,c_2732,c_3028,c_3734])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k8_relset_1(X2,X1,X0,X5),k1_zfmisc_1(X2))
    | ~ r2_hidden(X5,X3)
    | r2_hidden(k8_relset_1(X2,X1,X0,X5),X4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2553,plain,
    ( sP0(X0,X1,X2,X3,X4) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k8_relset_1(X2,X1,X0,X5),k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(X5,X3) != iProver_top
    | r2_hidden(k8_relset_1(X2,X1,X0,X5),X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9012,plain,
    ( sP0(sK8,sK7,sK6,X0,X1) != iProver_top
    | m1_subset_1(sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),k1_zfmisc_1(sK7)) != iProver_top
    | m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6)) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),X0) != iProver_top
    | r2_hidden(k8_relset_1(sK6,sK7,sK8,sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9008,c_2553])).

cnf(c_9038,plain,
    ( sP0(sK8,sK7,sK6,X0,X1) != iProver_top
    | m1_subset_1(sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),k1_zfmisc_1(sK7)) != iProver_top
    | m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6)) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),X0) != iProver_top
    | r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9012,c_9008])).

cnf(c_323,plain,
    ( r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_2727,plain,
    ( m1_subset_1(k6_funct_2(sK6,sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(sK6))) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2726])).

cnf(c_2733,plain,
    ( sP0(sK8,sK7,sK6,sK9,k6_funct_2(sK6,sK7,sK8,sK9)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2732])).

cnf(c_3029,plain,
    ( m1_subset_1(k6_funct_2(sK6,sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(sK6))) != iProver_top
    | m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6)) = iProver_top
    | r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3028])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | m1_subset_1(sK4(X0,X1,X2,X3,X5),k1_zfmisc_1(X1))
    | ~ r2_hidden(X5,X4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2805,plain,
    ( ~ sP0(X0,X1,X2,X3,k6_funct_2(sK6,sK7,sK8,sK9))
    | m1_subset_1(sK4(X0,X1,X2,X3,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(X2))
    | ~ r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3136,plain,
    ( ~ sP0(X0,X1,sK6,X2,k6_funct_2(sK6,sK7,sK8,sK9))
    | m1_subset_1(sK4(X0,X1,sK6,X2,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6))
    | ~ r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_2805])).

cnf(c_3617,plain,
    ( ~ sP0(sK8,sK7,sK6,sK9,k6_funct_2(sK6,sK7,sK8,sK9))
    | m1_subset_1(sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6))
    | ~ r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_3136])).

cnf(c_3618,plain,
    ( sP0(sK8,sK7,sK6,sK9,k6_funct_2(sK6,sK7,sK8,sK9)) != iProver_top
    | m1_subset_1(sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),k1_zfmisc_1(sK7)) = iProver_top
    | m1_subset_1(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k1_zfmisc_1(sK6)) != iProver_top
    | r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3617])).

cnf(c_9265,plain,
    ( sP0(sK8,sK7,sK6,X0,X1) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK6,sK9,sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10))),X0) != iProver_top
    | r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9038,c_32,c_323,c_2727,c_2733,c_3029,c_3618])).

cnf(c_9275,plain,
    ( sP0(sK8,sK7,sK6,sK10,X0) != iProver_top
    | r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),X0) = iProver_top
    | r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),k6_funct_2(sK6,sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4151,c_9265])).

cnf(c_9749,plain,
    ( r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),X0) = iProver_top
    | sP0(sK8,sK7,sK6,sK10,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9275,c_323])).

cnf(c_9750,plain,
    ( sP0(sK8,sK7,sK6,sK10,X0) != iProver_top
    | r2_hidden(sK5(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9749])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2549,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK5(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9757,plain,
    ( sP0(sK8,sK7,sK6,sK10,k6_funct_2(sK6,sK7,sK8,sK10)) != iProver_top
    | r1_tarski(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9750,c_2549])).

cnf(c_2729,plain,
    ( sP0(sK8,sK7,sK6,sK10,k6_funct_2(sK6,sK7,sK8,sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_2730,plain,
    ( sP0(sK8,sK7,sK6,sK10,k6_funct_2(sK6,sK7,sK8,sK10)) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2729])).

cnf(c_35,plain,
    ( r1_tarski(k6_funct_2(sK6,sK7,sK8,sK9),k6_funct_2(sK6,sK7,sK8,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(sK7))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_33,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9757,c_2730,c_35,c_33])).


%------------------------------------------------------------------------------
