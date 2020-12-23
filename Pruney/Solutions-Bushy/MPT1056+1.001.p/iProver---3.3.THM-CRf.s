%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1056+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:48 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  185 (2667 expanded)
%              Number of clauses        :  109 ( 618 expanded)
%              Number of leaves         :   20 (1008 expanded)
%              Depth                    :   31
%              Number of atoms          :  764 (30158 expanded)
%              Number of equality atoms :  291 (5651 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X4,X3,X1)
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,X0)
                             => ( r2_hidden(X5,X3)
                               => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                         => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,X0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,X0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_partfun1(X0,X1,X2,X3) != X4
          & ! [X5] :
              ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
              | ~ r2_hidden(X5,X3)
              | ~ m1_subset_1(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X4,X3,X1)
          & v1_funct_1(X4) )
     => ( k2_partfun1(X0,X1,X2,X3) != sK5
        & ! [X5] :
            ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(sK5,X5)
            | ~ r2_hidden(X5,X3)
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK5,X3,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k2_partfun1(X0,X1,X2,X3) != X4
              & ! [X5] :
                  ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,X3)
                  | ~ m1_subset_1(X5,X0) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
              & v1_funct_2(X4,X3,X1)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(X0))
          & ~ v1_xboole_0(X3) )
     => ( ? [X4] :
            ( k2_partfun1(X0,X1,X2,sK4) != X4
            & ! [X5] :
                ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                | ~ r2_hidden(X5,sK4)
                | ~ m1_subset_1(X5,X0) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
            & v1_funct_2(X4,sK4,X1)
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_partfun1(X0,X1,X2,X3) != X4
                  & ! [X5] :
                      ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                      | ~ r2_hidden(X5,X3)
                      | ~ m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                  & v1_funct_2(X4,X3,X1)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k2_partfun1(X0,X1,sK3,X3) != X4
                & ! [X5] :
                    ( k3_funct_2(X0,X1,sK3,X5) = k1_funct_1(X4,X5)
                    | ~ r2_hidden(X5,X3)
                    | ~ m1_subset_1(X5,X0) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                & v1_funct_2(X4,X3,X1)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,X0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k2_partfun1(X0,sK2,X2,X3) != X4
                    & ! [X5] :
                        ( k3_funct_2(X0,sK2,X2,X5) = k1_funct_1(X4,X5)
                        | ~ r2_hidden(X5,X3)
                        | ~ m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,sK2)))
                    & v1_funct_2(X4,X3,sK2)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_2(X2,X0,sK2)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k2_partfun1(X0,X1,X2,X3) != X4
                        & ! [X5] :
                            ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                            | ~ r2_hidden(X5,X3)
                            | ~ m1_subset_1(X5,X0) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(sK1,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(sK1,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,sK1) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK1))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
              & v1_funct_2(X2,sK1,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k2_partfun1(sK1,sK2,sK3,sK4) != sK5
    & ! [X5] :
        ( k3_funct_2(sK1,sK2,sK3,X5) = k1_funct_1(sK5,X5)
        | ~ r2_hidden(X5,sK4)
        | ~ m1_subset_1(X5,sK1) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_2(sK5,sK4,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & ~ v1_xboole_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f38,f46,f45,f44,f43,f42])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f62,f49])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f70,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f64,f49])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
            & m1_subset_1(sK0(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f40])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_2(sK5,sK4,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    k2_partfun1(sK1,sK2,sK3,sK4) != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X5] :
      ( k3_funct_2(sK1,sK2,sK3,X5) = k1_funct_1(sK5,X5)
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,sK1) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1600,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1611,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3027,plain,
    ( k2_partfun1(sK1,sK2,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1611])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1926,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2176,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK1,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_3341,plain,
    ( k2_partfun1(sK1,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3027,c_29,c_27,c_2176])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_685,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X4
    | X1 != X5
    | o_0_0_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_14])).

cnf(c_686,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_1591,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(k2_partfun1(X2,X0,X1,X3),X3,X0) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_3354,plain,
    ( sK2 = o_0_0_xboole_0
    | v1_funct_2(k7_relat_1(sK3,X0),X0,sK2) = iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_1591])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_429,plain,
    ( sK2 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_30])).

cnf(c_5615,plain,
    ( v1_funct_2(k7_relat_1(sK3,X0),X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3354,c_34,c_35,c_36,c_429])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_709,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X2)))
    | ~ v1_funct_1(X0)
    | X5 != X3
    | X1 != X4
    | o_0_0_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_12])).

cnf(c_710,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_1590,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(k2_partfun1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X0))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_3355,plain,
    ( sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_1590])).

cnf(c_5898,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3355,c_34,c_35,c_36,c_429])).

cnf(c_1598,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1605,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK0(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_560,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(X1,X0,X3),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0 ),
    inference(resolution,[status(thm)],[c_9,c_7])).

cnf(c_1595,plain,
    ( X0 = X1
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X0,X2,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(sK0(X2,X1,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_6539,plain,
    ( sK5 = X0
    | v1_funct_2(X0,sK4,sK2) != iProver_top
    | v1_funct_2(sK5,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,X0),sK4) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1595])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK4,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_40,plain,
    ( v1_funct_2(sK5,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6928,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | sK5 = X0
    | v1_funct_2(X0,sK4,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6539,c_39,c_40])).

cnf(c_6929,plain,
    ( sK5 = X0
    | v1_funct_2(X0,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,X0),sK4) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6928])).

cnf(c_6944,plain,
    ( k7_relat_1(sK3,sK4) = sK5
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5898,c_6929])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,negated_conjecture,
    ( k2_partfun1(sK1,sK2,sK3,sK4) != sK5 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3345,plain,
    ( k7_relat_1(sK3,sK4) != sK5 ),
    inference(demodulation,[status(thm)],[c_3341,c_20])).

cnf(c_7226,plain,
    ( m1_subset_1(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK4) = iProver_top
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6944,c_38,c_3345])).

cnf(c_7227,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK4) = iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7226])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1613,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2884,plain,
    ( v1_funct_1(k2_partfun1(sK1,sK2,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1613])).

cnf(c_1881,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2154,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_funct_1(k2_partfun1(sK1,sK2,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_2155,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2154])).

cnf(c_3167,plain,
    ( v1_funct_1(k2_partfun1(sK1,sK2,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2884,c_34,c_36,c_2155])).

cnf(c_3346,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3341,c_3167])).

cnf(c_7233,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7227,c_3346])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1609,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7235,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | r2_hidden(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7233,c_1609])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7276,plain,
    ( r2_hidden(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK4) = iProver_top
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7235,c_37])).

cnf(c_7277,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | r2_hidden(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_7276])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1607,plain,
    ( k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
    | r2_hidden(X2,X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7284,plain,
    ( k1_funct_1(k7_relat_1(X0,sK4),sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(X0,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7277,c_1607])).

cnf(c_19781,plain,
    ( k1_funct_1(k7_relat_1(X0,sK4),sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(X0,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5615,c_7284])).

cnf(c_20567,plain,
    ( k1_funct_1(k7_relat_1(X0,sK4),sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(X0,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19781,c_38])).

cnf(c_20577,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK4),sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_20567])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1839,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1840,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1839])).

cnf(c_20894,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK4),sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20577,c_36,c_1840])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_589,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0
    | k1_funct_1(X3,sK0(X1,X0,X3)) != k1_funct_1(X0,sK0(X1,X0,X3)) ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_1594,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK0(X2,X1,X0)) != k1_funct_1(X1,sK0(X2,X1,X0))
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X0,X2,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_20898,plain,
    ( k1_funct_1(sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) != k1_funct_1(sK5,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | k7_relat_1(sK3,sK4) = sK5
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,X0) != iProver_top
    | v1_funct_2(sK5,sK4,X0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20894,c_1594])).

cnf(c_1602,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1608,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2607,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_1608])).

cnf(c_7282,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7277,c_2607])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1610,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3805,plain,
    ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1610])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3918,plain,
    ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3805,c_32,c_34,c_35])).

cnf(c_7620,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7282,c_3918])).

cnf(c_7805,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5615,c_7620])).

cnf(c_15099,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7805,c_38])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1606,plain,
    ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7283,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK5,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,k7_relat_1(sK3,sK4)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7277,c_1606])).

cnf(c_7303,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK5,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7282,c_7283])).

cnf(c_7800,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK5,sK0(sK4,sK5,k7_relat_1(sK3,sK4)))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5615,c_7303])).

cnf(c_15093,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK5,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7800,c_38])).

cnf(c_15102,plain,
    ( k1_funct_1(sK3,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) = k1_funct_1(sK5,sK0(sK4,sK5,k7_relat_1(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_15099,c_15093])).

cnf(c_20966,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | v1_funct_2(sK5,sK4,X0) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,sK4),sK4,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20898,c_39,c_3345,c_15102])).

cnf(c_20967,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,X0) != iProver_top
    | v1_funct_2(sK5,sK4,X0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_20966])).

cnf(c_20977,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,X0) != iProver_top
    | v1_funct_2(sK5,sK4,X0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20967,c_3346])).

cnf(c_20981,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top
    | v1_funct_2(sK5,sK4,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5898,c_20977])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21713,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK4),sK4,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20981,c_38,c_40,c_41])).

cnf(c_21718,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5615,c_21713])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21718,c_38])).


%------------------------------------------------------------------------------
