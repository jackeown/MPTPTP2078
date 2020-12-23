%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:50 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 384 expanded)
%              Number of clauses        :   59 (  82 expanded)
%              Number of leaves         :   17 ( 147 expanded)
%              Depth                    :   18
%              Number of atoms          :  702 (2863 expanded)
%              Number of equality atoms :  127 ( 449 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                      & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
          & m1_subset_1(X4,X0) )
     => ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK6) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),sK6),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),sK6))
        & m1_subset_1(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
          & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),sK5,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,sK5),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,sK5),X4))
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(sK5,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
              & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k3_funct_2(X0,k2_zfmisc_1(X1,sK4),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,sK4,X3),X4),k3_funct_2(X0,sK4,k5_funct_2(X0,X1,sK4,X3),X4))
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,sK4))))
            & v1_funct_2(X3,X0,k2_zfmisc_1(X1,sK4))
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k3_funct_2(X0,k2_zfmisc_1(sK3,X2),X3,X4) != k4_tarski(k3_funct_2(X0,sK3,k4_funct_2(X0,sK3,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,sK3,X2,X3),X4))
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(sK3,X2))))
                & v1_funct_2(X3,X0,k2_zfmisc_1(sK3,X2))
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                        & m1_subset_1(X4,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(sK2,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(sK2,X1,k4_funct_2(sK2,X1,X2,X3),X4),k3_funct_2(sK2,X2,k5_funct_2(sK2,X1,X2,X3),X4))
                      & m1_subset_1(X4,sK2) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,sK2,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6) != k4_tarski(k3_funct_2(sK2,sK3,k4_funct_2(sK2,sK3,sK4,sK5),sK6),k3_funct_2(sK2,sK4,k5_funct_2(sK2,sK3,sK4,sK5),sK6))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_zfmisc_1(sK3,sK4))))
    & v1_funct_2(sK5,sK2,k2_zfmisc_1(sK3,sK4))
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f29,f42,f41,f40,f39,f38])).

fof(f67,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_zfmisc_1(sK3,sK4)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                        & v1_funct_2(X4,X0,X1)
                        & v1_funct_1(X4) )
                     => ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              | ~ m1_subset_1(X5,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X4,sK0(X0,X1,X2,X3,X4)) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK0(X0,X1,X2,X3,X4)))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ( k3_funct_2(X0,X1,X4,sK0(X0,X1,X2,X3,X4)) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK0(X0,X1,X2,X3,X4)))
                            & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
      | ~ m1_subset_1(X6,X0)
      | k4_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | ~ v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    v1_funct_2(sK5,sK2,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                        & v1_funct_2(X4,X0,X2)
                        & v1_funct_1(X4) )
                     => ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              | ~ m1_subset_1(X5,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X2,X4,sK1(X0,X1,X2,X3,X4)) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK1(X0,X1,X2,X3,X4)))
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ( k3_funct_2(X0,X2,X4,sK1(X0,X1,X2,X3,X4)) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK1(X0,X1,X2,X3,X4)))
                            & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
      | ~ m1_subset_1(X6,X0)
      | k5_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X4,X0,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | ~ v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6) != k4_tarski(k3_funct_2(sK2,sK3,k4_funct_2(sK2,sK3,sK4,sK5),sK6),k3_funct_2(sK2,sK4,k5_funct_2(sK2,sK3,sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_492,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_936,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_zfmisc_1(sK3,sK4)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_491,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_zfmisc_1(sK3,sK4)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_937,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_zfmisc_1(sK3,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_2(k4_funct_2(X1,X2,X3,X0),X1,X2)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(k4_funct_2(X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k4_funct_2(X1,X2,X3,X0))
    | k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X0),X4) = k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X0,X4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k4_funct_2(X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | v1_funct_2(k4_funct_2(X1,X2,X3,X0),X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | m1_subset_1(k4_funct_2(X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_159,plain,
    ( ~ v1_funct_1(X0)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X0),X4) = k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X0,X4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_9,c_8,c_7])).

cnf(c_160,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X0),X4) = k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X0,X4)) ),
    inference(renaming,[status(thm)],[c_159])).

cnf(c_484,plain,
    ( ~ v1_funct_2(X0_49,X0_50,k2_zfmisc_1(X1_50,X2_50))
    | ~ m1_subset_1(X1_49,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_zfmisc_1(X1_50,X2_50))))
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X0_50)
    | ~ v1_funct_1(X0_49)
    | k3_funct_2(X0_50,X1_50,k4_funct_2(X0_50,X1_50,X2_50,X0_49),X1_49) = k1_mcart_1(k3_funct_2(X0_50,k2_zfmisc_1(X1_50,X2_50),X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_160])).

cnf(c_944,plain,
    ( k3_funct_2(X0_50,X1_50,k4_funct_2(X0_50,X1_50,X2_50,X0_49),X1_49) = k1_mcart_1(k3_funct_2(X0_50,k2_zfmisc_1(X1_50,X2_50),X0_49,X1_49))
    | v1_funct_2(X0_49,X0_50,k2_zfmisc_1(X1_50,X2_50)) != iProver_top
    | m1_subset_1(X1_49,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_zfmisc_1(X1_50,X2_50)))) != iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_3723,plain,
    ( k3_funct_2(sK2,sK3,k4_funct_2(sK2,sK3,sK4,sK5),X0_49) = k1_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,X0_49))
    | v1_funct_2(sK5,sK2,k2_zfmisc_1(sK3,sK4)) != iProver_top
    | m1_subset_1(X0_49,sK2) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_944])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,plain,
    ( v1_funct_2(sK5,sK2,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3903,plain,
    ( k3_funct_2(sK2,sK3,k4_funct_2(sK2,sK3,sK4,sK5),X0_49) = k1_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,X0_49))
    | m1_subset_1(X0_49,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3723,c_25,c_26,c_27,c_28,c_29])).

cnf(c_3911,plain,
    ( k3_funct_2(sK2,sK3,k4_funct_2(sK2,sK3,sK4,sK5),sK6) = k1_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_936,c_3903])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_2(k5_funct_2(X1,X2,X3,X0),X1,X3)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(k5_funct_2(X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k5_funct_2(X1,X2,X3,X0))
    | k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X0),X4) = k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X0,X4)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k5_funct_2(X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | v1_funct_2(k5_funct_2(X1,X2,X3,X0),X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | m1_subset_1(k5_funct_2(X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_150,plain,
    ( ~ v1_funct_1(X0)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X0),X4) = k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X0,X4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_12,c_11,c_10])).

cnf(c_151,plain,
    ( ~ v1_funct_2(X0,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X0),X4) = k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X0,X4)) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_485,plain,
    ( ~ v1_funct_2(X0_49,X0_50,k2_zfmisc_1(X1_50,X2_50))
    | ~ m1_subset_1(X1_49,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_zfmisc_1(X1_50,X2_50))))
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X0_50)
    | ~ v1_funct_1(X0_49)
    | k3_funct_2(X0_50,X2_50,k5_funct_2(X0_50,X1_50,X2_50,X0_49),X1_49) = k2_mcart_1(k3_funct_2(X0_50,k2_zfmisc_1(X1_50,X2_50),X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_151])).

cnf(c_943,plain,
    ( k3_funct_2(X0_50,X1_50,k5_funct_2(X0_50,X2_50,X1_50,X0_49),X1_49) = k2_mcart_1(k3_funct_2(X0_50,k2_zfmisc_1(X2_50,X1_50),X0_49,X1_49))
    | v1_funct_2(X0_49,X0_50,k2_zfmisc_1(X2_50,X1_50)) != iProver_top
    | m1_subset_1(X1_49,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_zfmisc_1(X2_50,X1_50)))) != iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_3092,plain,
    ( k3_funct_2(sK2,sK4,k5_funct_2(sK2,sK3,sK4,sK5),X0_49) = k2_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,X0_49))
    | v1_funct_2(sK5,sK2,k2_zfmisc_1(sK3,sK4)) != iProver_top
    | m1_subset_1(X0_49,sK2) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_943])).

cnf(c_3254,plain,
    ( k3_funct_2(sK2,sK4,k5_funct_2(sK2,sK3,sK4,sK5),X0_49) = k2_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,X0_49))
    | m1_subset_1(X0_49,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3092,c_25,c_26,c_27,c_28,c_29])).

cnf(c_3262,plain,
    ( k3_funct_2(sK2,sK4,k5_funct_2(sK2,sK3,sK4,sK5),sK6) = k2_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_936,c_3254])).

cnf(c_17,negated_conjecture,
    ( k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6) != k4_tarski(k3_funct_2(sK2,sK3,k4_funct_2(sK2,sK3,sK4,sK5),sK6),k3_funct_2(sK2,sK4,k5_funct_2(sK2,sK3,sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_493,negated_conjecture,
    ( k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6) != k4_tarski(k3_funct_2(sK2,sK3,k4_funct_2(sK2,sK3,sK4,sK5),sK6),k3_funct_2(sK2,sK4,k5_funct_2(sK2,sK3,sK4,sK5),sK6)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3310,plain,
    ( k4_tarski(k3_funct_2(sK2,sK3,k4_funct_2(sK2,sK3,sK4,sK5),sK6),k2_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6))) != k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6) ),
    inference(demodulation,[status(thm)],[c_3262,c_493])).

cnf(c_4020,plain,
    ( k4_tarski(k1_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6)),k2_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6))) != k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6) ),
    inference(demodulation,[status(thm)],[c_3911,c_3310])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_15])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0_49,k2_zfmisc_1(X0_50,X1_50))
    | k4_tarski(k1_mcart_1(X0_49),k2_mcart_1(X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_280])).

cnf(c_2830,plain,
    ( ~ r2_hidden(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6),k2_zfmisc_1(sK3,sK4))
    | k4_tarski(k1_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6)),k2_mcart_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6))) = k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_13,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_495,plain,
    ( v1_xboole_0(X0_50)
    | v1_xboole_0(X1_50)
    | ~ v1_xboole_0(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1836,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,sK4))
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_494,plain,
    ( r2_hidden(X0_49,X0_50)
    | ~ m1_subset_1(X0_49,X0_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1695,plain,
    ( r2_hidden(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6),k2_zfmisc_1(sK3,sK4))
    | ~ m1_subset_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6),k2_zfmisc_1(sK3,sK4))
    | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_502,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X1_49,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | m1_subset_1(k3_funct_2(X0_50,X1_50,X0_49,X1_49),X1_50)
    | v1_xboole_0(X0_50)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1269,plain,
    ( ~ v1_funct_2(X0_49,sK2,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_50)))
    | m1_subset_1(k3_funct_2(sK2,X0_50,X0_49,sK6),X0_50)
    | ~ m1_subset_1(sK6,sK2)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_1514,plain,
    ( ~ v1_funct_2(sK5,sK2,k2_zfmisc_1(sK3,sK4))
    | m1_subset_1(k3_funct_2(sK2,k2_zfmisc_1(sK3,sK4),sK5,sK6),k2_zfmisc_1(sK3,sK4))
    | ~ m1_subset_1(sK6,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_zfmisc_1(sK3,sK4))))
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4020,c_2830,c_1836,c_1695,c_1514,c_18,c_19,c_20,c_21,c_22,c_23,c_24])).


%------------------------------------------------------------------------------
