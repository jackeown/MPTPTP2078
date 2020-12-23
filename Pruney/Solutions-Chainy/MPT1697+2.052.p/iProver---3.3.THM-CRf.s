%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:33 EST 2020

% Result     : Theorem 23.47s
% Output     : CNFRefutation 23.47s
% Verified   : 
% Statistics : Number of formulae       :  273 (3852 expanded)
%              Number of clauses        :  180 (1200 expanded)
%              Number of leaves         :   23 (1257 expanded)
%              Depth                    :   28
%              Number of atoms          : 1385 (38025 expanded)
%              Number of equality atoms :  574 (9181 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4
          | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK5,X3,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
              & v1_funct_2(X5,X3,X1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          & v1_funct_2(X4,X2,X1)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4
              | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK4,X2,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                    | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                  & v1_funct_2(X5,X3,X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(X4,X2,X1)
              & v1_funct_1(X4) )
          & r1_subset_1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(X0))
          & ~ v1_xboole_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4
                  | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
                & v1_funct_2(X5,sK3,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X5,X3,X1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                  & v1_funct_2(X4,X2,X1)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(X0))
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4
                      | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
                & v1_funct_2(X4,sK2,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                        & v1_funct_2(X5,X3,sK1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                    & v1_funct_2(X4,X2,sK1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                              | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                    & r1_subset_1(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK5,sK3,sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & r1_subset_1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f43,f55,f54,f53,f52,f51,f50])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f64,f61])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f95,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1247,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2043,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_505,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_16,c_12,c_11])).

cnf(c_510,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_509])).

cnf(c_569,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_13,c_510])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_16,c_13,c_12,c_11])).

cnf(c_574,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_573])).

cnf(c_1231,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | v1_xboole_0(X2_54)
    | k1_relat_1(X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_574])).

cnf(c_2059,plain,
    ( k1_relat_1(X0_54) = X1_54
    | v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1231])).

cnf(c_7076,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_2059])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2146,plain,
    ( ~ v1_funct_2(X0_54,X1_54,sK1)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1)))
    | ~ v1_funct_1(X0_54)
    | v1_xboole_0(sK1)
    | k1_relat_1(X0_54) = X1_54 ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_2283,plain,
    ( ~ v1_funct_2(sK5,X0_54,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2146])).

cnf(c_2343,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2283])).

cnf(c_7115,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7076,c_36,c_27,c_26,c_25,c_2343])).

cnf(c_1254,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2037,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_3167,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_2037])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1259,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2032,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1259])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_5])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_12,c_11,c_5])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k7_relat_1(X0_54,X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_529])).

cnf(c_2058,plain,
    ( k7_relat_1(X0_54,X1_54) = X0_54
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_4251,plain,
    ( k7_relat_1(k1_xboole_0,X0_54) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2032,c_2058])).

cnf(c_8,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1255,plain,
    ( r1_xboole_0(k1_relat_1(X0_54),X1_54)
    | ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,X1_54) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2036,plain,
    ( k7_relat_1(X0_54,X1_54) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_54),X1_54) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_4419,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0_54) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4251,c_2036])).

cnf(c_3169,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_2037])).

cnf(c_4831,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4419,c_3169])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1258,plain,
    ( ~ r1_xboole_0(X0_54,k1_relat_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | k7_relat_1(X1_54,X0_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2033,plain,
    ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(X1_54,k1_relat_1(X0_54)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_4839,plain,
    ( k7_relat_1(X0_54,k1_relat_1(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_4831,c_2033])).

cnf(c_4945,plain,
    ( k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3167,c_4839])).

cnf(c_4998,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4945,c_2036])).

cnf(c_6734,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4998,c_3167])).

cnf(c_7117,plain,
    ( r1_xboole_0(sK3,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7115,c_6734])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1261,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | k1_setfam_1(k2_tarski(X0_54,X1_54)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2030,plain,
    ( k1_setfam_1(k2_tarski(X0_54,X1_54)) = k1_xboole_0
    | r1_xboole_0(X0_54,X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_6739,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK5),k1_relat_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6734,c_2030])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1257,plain,
    ( ~ v1_relat_1(X0_54)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0_54),X1_54)) = k1_relat_1(k7_relat_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2034,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0_54),X1_54)) = k1_relat_1(k7_relat_1(X0_54,X1_54))
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_3799,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_54)) = k1_relat_1(k7_relat_1(sK5,X0_54)) ),
    inference(superposition,[status(thm)],[c_3167,c_2034])).

cnf(c_6744,plain,
    ( k1_relat_1(k7_relat_1(sK5,k1_relat_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6739,c_3799])).

cnf(c_6745,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6744,c_4945])).

cnf(c_7127,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7117,c_6745])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1256,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_54),X1_54)
    | ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,X1_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2035,plain,
    ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_54),X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_7135,plain,
    ( k7_relat_1(sK5,X0_54) = k1_xboole_0
    | r1_xboole_0(sK3,X0_54) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7115,c_2035])).

cnf(c_7144,plain,
    ( r1_xboole_0(sK3,X0_54) != iProver_top
    | k7_relat_1(sK5,X0_54) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7135,c_3167])).

cnf(c_7145,plain,
    ( k7_relat_1(sK5,X0_54) = k1_xboole_0
    | r1_xboole_0(sK3,X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_7144])).

cnf(c_35864,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7127,c_7145])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1244,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2046,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_3168,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_2037])).

cnf(c_4946,plain,
    ( k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3168,c_4839])).

cnf(c_5594,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4946,c_2036])).

cnf(c_6791,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5594,c_3168])).

cnf(c_6795,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6791,c_6745])).

cnf(c_6797,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6795,c_2035])).

cnf(c_7090,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6797,c_3168])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1253,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2038,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_3954,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_2038])).

cnf(c_48,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4071,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3954,c_48])).

cnf(c_10,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_492,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_493,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_495,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_35,c_33])).

cnf(c_1233,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_2057,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_3235,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2057,c_2030])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1241,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2049,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1260,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k1_setfam_1(k2_tarski(X2_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2031,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k1_setfam_1(k2_tarski(X1_54,X2_54))
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_2750,plain,
    ( k9_subset_1(sK0,X0_54,sK3) = k1_setfam_1(k2_tarski(X0_54,sK3)) ),
    inference(superposition,[status(thm)],[c_2049,c_2031])).

cnf(c_24,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1248,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3000,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2750,c_1248])).

cnf(c_3818,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3235,c_3000])).

cnf(c_4074,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4071,c_3818])).

cnf(c_3955,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_2038])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_45,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4096,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3955,c_45])).

cnf(c_4099,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4074,c_4096])).

cnf(c_7092,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7090,c_4099])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_217,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_23,c_22,c_21])).

cnf(c_218,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X5)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_1234,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_2056,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
    | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1234])).

cnf(c_6000,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4071,c_2056])).

cnf(c_39,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_42,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_49,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15330,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6000,c_39,c_42,c_48,c_49,c_50])).

cnf(c_15331,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_15330])).

cnf(c_15337,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4096,c_15331])).

cnf(c_40,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_46,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16850,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15337,c_40,c_45,c_46,c_47])).

cnf(c_16851,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_16850])).

cnf(c_16856,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2750,c_16851])).

cnf(c_16857,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16856,c_3235])).

cnf(c_16858,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16857,c_2750])).

cnf(c_16859,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16858,c_3235,c_7090])).

cnf(c_16860,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16859])).

cnf(c_34063,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7092,c_37,c_34,c_32,c_16860])).

cnf(c_1249,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2042,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
    | v1_xboole_0(X5_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_1251,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2040,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_xboole_0(X5_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1251])).

cnf(c_4355,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_2040,c_2038])).

cnf(c_11470,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_2042,c_4355])).

cnf(c_18566,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_11470])).

cnf(c_18583,plain,
    ( v1_funct_1(X2_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18566,c_39,c_42,c_48,c_49])).

cnf(c_18584,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_18583])).

cnf(c_18590,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_18584])).

cnf(c_19043,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18590,c_40,c_45,c_46])).

cnf(c_19044,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_19043])).

cnf(c_19049,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_19044])).

cnf(c_38,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19054,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19049,c_38,c_41])).

cnf(c_34065,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34063,c_19054])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_210,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_23,c_22,c_21])).

cnf(c_211,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X5)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_1235,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_211])).

cnf(c_2055,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
    | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_4775,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4071,c_2055])).

cnf(c_5599,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4775,c_39,c_42,c_48,c_49,c_50])).

cnf(c_5600,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_5599])).

cnf(c_5606,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4096,c_5600])).

cnf(c_5712,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5606,c_40,c_45,c_46,c_47])).

cnf(c_5713,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_5712])).

cnf(c_5718,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2750,c_5713])).

cnf(c_5719,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5718,c_3235])).

cnf(c_5720,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5719,c_2750])).

cnf(c_5721,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5720,c_3235])).

cnf(c_5722,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5721])).

cnf(c_25274,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5721,c_37,c_34,c_32,c_5722])).

cnf(c_25275,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_25274])).

cnf(c_25276,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_25275,c_7090])).

cnf(c_25277,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25276,c_19054])).

cnf(c_34066,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34065,c_25277])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35864,c_34066])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 23.47/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.47/3.50  
% 23.47/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.47/3.50  
% 23.47/3.50  ------  iProver source info
% 23.47/3.50  
% 23.47/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.47/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.47/3.50  git: non_committed_changes: false
% 23.47/3.50  git: last_make_outside_of_git: false
% 23.47/3.50  
% 23.47/3.50  ------ 
% 23.47/3.50  
% 23.47/3.50  ------ Input Options
% 23.47/3.50  
% 23.47/3.50  --out_options                           all
% 23.47/3.50  --tptp_safe_out                         true
% 23.47/3.50  --problem_path                          ""
% 23.47/3.50  --include_path                          ""
% 23.47/3.50  --clausifier                            res/vclausify_rel
% 23.47/3.50  --clausifier_options                    ""
% 23.47/3.50  --stdin                                 false
% 23.47/3.50  --stats_out                             all
% 23.47/3.50  
% 23.47/3.50  ------ General Options
% 23.47/3.50  
% 23.47/3.50  --fof                                   false
% 23.47/3.50  --time_out_real                         305.
% 23.47/3.50  --time_out_virtual                      -1.
% 23.47/3.50  --symbol_type_check                     false
% 23.47/3.50  --clausify_out                          false
% 23.47/3.50  --sig_cnt_out                           false
% 23.47/3.50  --trig_cnt_out                          false
% 23.47/3.50  --trig_cnt_out_tolerance                1.
% 23.47/3.50  --trig_cnt_out_sk_spl                   false
% 23.47/3.50  --abstr_cl_out                          false
% 23.47/3.50  
% 23.47/3.50  ------ Global Options
% 23.47/3.50  
% 23.47/3.50  --schedule                              default
% 23.47/3.50  --add_important_lit                     false
% 23.47/3.50  --prop_solver_per_cl                    1000
% 23.47/3.50  --min_unsat_core                        false
% 23.47/3.50  --soft_assumptions                      false
% 23.47/3.50  --soft_lemma_size                       3
% 23.47/3.50  --prop_impl_unit_size                   0
% 23.47/3.50  --prop_impl_unit                        []
% 23.47/3.50  --share_sel_clauses                     true
% 23.47/3.50  --reset_solvers                         false
% 23.47/3.50  --bc_imp_inh                            [conj_cone]
% 23.47/3.50  --conj_cone_tolerance                   3.
% 23.47/3.50  --extra_neg_conj                        none
% 23.47/3.50  --large_theory_mode                     true
% 23.47/3.50  --prolific_symb_bound                   200
% 23.47/3.50  --lt_threshold                          2000
% 23.47/3.50  --clause_weak_htbl                      true
% 23.47/3.50  --gc_record_bc_elim                     false
% 23.47/3.50  
% 23.47/3.50  ------ Preprocessing Options
% 23.47/3.50  
% 23.47/3.50  --preprocessing_flag                    true
% 23.47/3.50  --time_out_prep_mult                    0.1
% 23.47/3.50  --splitting_mode                        input
% 23.47/3.50  --splitting_grd                         true
% 23.47/3.50  --splitting_cvd                         false
% 23.47/3.50  --splitting_cvd_svl                     false
% 23.47/3.50  --splitting_nvd                         32
% 23.47/3.50  --sub_typing                            true
% 23.47/3.50  --prep_gs_sim                           true
% 23.47/3.50  --prep_unflatten                        true
% 23.47/3.50  --prep_res_sim                          true
% 23.47/3.50  --prep_upred                            true
% 23.47/3.50  --prep_sem_filter                       exhaustive
% 23.47/3.50  --prep_sem_filter_out                   false
% 23.47/3.50  --pred_elim                             true
% 23.47/3.50  --res_sim_input                         true
% 23.47/3.50  --eq_ax_congr_red                       true
% 23.47/3.50  --pure_diseq_elim                       true
% 23.47/3.50  --brand_transform                       false
% 23.47/3.50  --non_eq_to_eq                          false
% 23.47/3.50  --prep_def_merge                        true
% 23.47/3.50  --prep_def_merge_prop_impl              false
% 23.47/3.50  --prep_def_merge_mbd                    true
% 23.47/3.50  --prep_def_merge_tr_red                 false
% 23.47/3.50  --prep_def_merge_tr_cl                  false
% 23.47/3.50  --smt_preprocessing                     true
% 23.47/3.50  --smt_ac_axioms                         fast
% 23.47/3.50  --preprocessed_out                      false
% 23.47/3.50  --preprocessed_stats                    false
% 23.47/3.50  
% 23.47/3.50  ------ Abstraction refinement Options
% 23.47/3.50  
% 23.47/3.50  --abstr_ref                             []
% 23.47/3.50  --abstr_ref_prep                        false
% 23.47/3.50  --abstr_ref_until_sat                   false
% 23.47/3.50  --abstr_ref_sig_restrict                funpre
% 23.47/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.47/3.50  --abstr_ref_under                       []
% 23.47/3.50  
% 23.47/3.50  ------ SAT Options
% 23.47/3.50  
% 23.47/3.50  --sat_mode                              false
% 23.47/3.50  --sat_fm_restart_options                ""
% 23.47/3.50  --sat_gr_def                            false
% 23.47/3.50  --sat_epr_types                         true
% 23.47/3.50  --sat_non_cyclic_types                  false
% 23.47/3.50  --sat_finite_models                     false
% 23.47/3.50  --sat_fm_lemmas                         false
% 23.47/3.50  --sat_fm_prep                           false
% 23.47/3.50  --sat_fm_uc_incr                        true
% 23.47/3.50  --sat_out_model                         small
% 23.47/3.50  --sat_out_clauses                       false
% 23.47/3.50  
% 23.47/3.50  ------ QBF Options
% 23.47/3.50  
% 23.47/3.50  --qbf_mode                              false
% 23.47/3.50  --qbf_elim_univ                         false
% 23.47/3.50  --qbf_dom_inst                          none
% 23.47/3.50  --qbf_dom_pre_inst                      false
% 23.47/3.50  --qbf_sk_in                             false
% 23.47/3.50  --qbf_pred_elim                         true
% 23.47/3.50  --qbf_split                             512
% 23.47/3.50  
% 23.47/3.50  ------ BMC1 Options
% 23.47/3.50  
% 23.47/3.50  --bmc1_incremental                      false
% 23.47/3.50  --bmc1_axioms                           reachable_all
% 23.47/3.50  --bmc1_min_bound                        0
% 23.47/3.50  --bmc1_max_bound                        -1
% 23.47/3.50  --bmc1_max_bound_default                -1
% 23.47/3.50  --bmc1_symbol_reachability              true
% 23.47/3.50  --bmc1_property_lemmas                  false
% 23.47/3.50  --bmc1_k_induction                      false
% 23.47/3.50  --bmc1_non_equiv_states                 false
% 23.47/3.50  --bmc1_deadlock                         false
% 23.47/3.50  --bmc1_ucm                              false
% 23.47/3.50  --bmc1_add_unsat_core                   none
% 23.47/3.50  --bmc1_unsat_core_children              false
% 23.47/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.47/3.50  --bmc1_out_stat                         full
% 23.47/3.50  --bmc1_ground_init                      false
% 23.47/3.50  --bmc1_pre_inst_next_state              false
% 23.47/3.50  --bmc1_pre_inst_state                   false
% 23.47/3.50  --bmc1_pre_inst_reach_state             false
% 23.47/3.50  --bmc1_out_unsat_core                   false
% 23.47/3.50  --bmc1_aig_witness_out                  false
% 23.47/3.50  --bmc1_verbose                          false
% 23.47/3.50  --bmc1_dump_clauses_tptp                false
% 23.47/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.47/3.50  --bmc1_dump_file                        -
% 23.47/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.47/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.47/3.50  --bmc1_ucm_extend_mode                  1
% 23.47/3.50  --bmc1_ucm_init_mode                    2
% 23.47/3.50  --bmc1_ucm_cone_mode                    none
% 23.47/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.47/3.50  --bmc1_ucm_relax_model                  4
% 23.47/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.47/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.47/3.50  --bmc1_ucm_layered_model                none
% 23.47/3.50  --bmc1_ucm_max_lemma_size               10
% 23.47/3.50  
% 23.47/3.50  ------ AIG Options
% 23.47/3.50  
% 23.47/3.50  --aig_mode                              false
% 23.47/3.50  
% 23.47/3.50  ------ Instantiation Options
% 23.47/3.50  
% 23.47/3.50  --instantiation_flag                    true
% 23.47/3.50  --inst_sos_flag                         true
% 23.47/3.50  --inst_sos_phase                        true
% 23.47/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.47/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.47/3.50  --inst_lit_sel_side                     num_symb
% 23.47/3.50  --inst_solver_per_active                1400
% 23.47/3.50  --inst_solver_calls_frac                1.
% 23.47/3.50  --inst_passive_queue_type               priority_queues
% 23.47/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.47/3.50  --inst_passive_queues_freq              [25;2]
% 23.47/3.50  --inst_dismatching                      true
% 23.47/3.50  --inst_eager_unprocessed_to_passive     true
% 23.47/3.50  --inst_prop_sim_given                   true
% 23.47/3.50  --inst_prop_sim_new                     false
% 23.47/3.50  --inst_subs_new                         false
% 23.47/3.50  --inst_eq_res_simp                      false
% 23.47/3.50  --inst_subs_given                       false
% 23.47/3.50  --inst_orphan_elimination               true
% 23.47/3.50  --inst_learning_loop_flag               true
% 23.47/3.50  --inst_learning_start                   3000
% 23.47/3.50  --inst_learning_factor                  2
% 23.47/3.50  --inst_start_prop_sim_after_learn       3
% 23.47/3.50  --inst_sel_renew                        solver
% 23.47/3.50  --inst_lit_activity_flag                true
% 23.47/3.50  --inst_restr_to_given                   false
% 23.47/3.50  --inst_activity_threshold               500
% 23.47/3.50  --inst_out_proof                        true
% 23.47/3.50  
% 23.47/3.50  ------ Resolution Options
% 23.47/3.50  
% 23.47/3.50  --resolution_flag                       true
% 23.47/3.50  --res_lit_sel                           adaptive
% 23.47/3.50  --res_lit_sel_side                      none
% 23.47/3.50  --res_ordering                          kbo
% 23.47/3.50  --res_to_prop_solver                    active
% 23.47/3.50  --res_prop_simpl_new                    false
% 23.47/3.50  --res_prop_simpl_given                  true
% 23.47/3.50  --res_passive_queue_type                priority_queues
% 23.47/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.47/3.50  --res_passive_queues_freq               [15;5]
% 23.47/3.50  --res_forward_subs                      full
% 23.47/3.50  --res_backward_subs                     full
% 23.47/3.50  --res_forward_subs_resolution           true
% 23.47/3.50  --res_backward_subs_resolution          true
% 23.47/3.50  --res_orphan_elimination                true
% 23.47/3.50  --res_time_limit                        2.
% 23.47/3.50  --res_out_proof                         true
% 23.47/3.50  
% 23.47/3.50  ------ Superposition Options
% 23.47/3.50  
% 23.47/3.50  --superposition_flag                    true
% 23.47/3.50  --sup_passive_queue_type                priority_queues
% 23.47/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.47/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.47/3.50  --demod_completeness_check              fast
% 23.47/3.50  --demod_use_ground                      true
% 23.47/3.50  --sup_to_prop_solver                    passive
% 23.47/3.50  --sup_prop_simpl_new                    true
% 23.47/3.50  --sup_prop_simpl_given                  true
% 23.47/3.50  --sup_fun_splitting                     true
% 23.47/3.50  --sup_smt_interval                      50000
% 23.47/3.50  
% 23.47/3.50  ------ Superposition Simplification Setup
% 23.47/3.50  
% 23.47/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.47/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.47/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.47/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.47/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.47/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.47/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.47/3.50  --sup_immed_triv                        [TrivRules]
% 23.47/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.47/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.47/3.50  --sup_immed_bw_main                     []
% 23.47/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.47/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.47/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.47/3.50  --sup_input_bw                          []
% 23.47/3.50  
% 23.47/3.50  ------ Combination Options
% 23.47/3.50  
% 23.47/3.50  --comb_res_mult                         3
% 23.47/3.50  --comb_sup_mult                         2
% 23.47/3.50  --comb_inst_mult                        10
% 23.47/3.50  
% 23.47/3.50  ------ Debug Options
% 23.47/3.50  
% 23.47/3.50  --dbg_backtrace                         false
% 23.47/3.50  --dbg_dump_prop_clauses                 false
% 23.47/3.50  --dbg_dump_prop_clauses_file            -
% 23.47/3.50  --dbg_out_stat                          false
% 23.47/3.50  ------ Parsing...
% 23.47/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.47/3.50  
% 23.47/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 23.47/3.50  
% 23.47/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.47/3.50  
% 23.47/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.47/3.50  ------ Proving...
% 23.47/3.50  ------ Problem Properties 
% 23.47/3.50  
% 23.47/3.50  
% 23.47/3.50  clauses                                 32
% 23.47/3.50  conjectures                             13
% 23.47/3.50  EPR                                     9
% 23.47/3.50  Horn                                    25
% 23.47/3.50  unary                                   14
% 23.47/3.50  binary                                  6
% 23.47/3.50  lits                                    130
% 23.47/3.50  lits eq                                 19
% 23.47/3.50  fd_pure                                 0
% 23.47/3.50  fd_pseudo                               0
% 23.47/3.50  fd_cond                                 0
% 23.47/3.50  fd_pseudo_cond                          1
% 23.47/3.50  AC symbols                              0
% 23.47/3.50  
% 23.47/3.50  ------ Schedule dynamic 5 is on 
% 23.47/3.50  
% 23.47/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.47/3.50  
% 23.47/3.50  
% 23.47/3.50  ------ 
% 23.47/3.50  Current options:
% 23.47/3.50  ------ 
% 23.47/3.50  
% 23.47/3.50  ------ Input Options
% 23.47/3.50  
% 23.47/3.50  --out_options                           all
% 23.47/3.50  --tptp_safe_out                         true
% 23.47/3.50  --problem_path                          ""
% 23.47/3.50  --include_path                          ""
% 23.47/3.50  --clausifier                            res/vclausify_rel
% 23.47/3.50  --clausifier_options                    ""
% 23.47/3.50  --stdin                                 false
% 23.47/3.50  --stats_out                             all
% 23.47/3.50  
% 23.47/3.50  ------ General Options
% 23.47/3.50  
% 23.47/3.50  --fof                                   false
% 23.47/3.50  --time_out_real                         305.
% 23.47/3.50  --time_out_virtual                      -1.
% 23.47/3.50  --symbol_type_check                     false
% 23.47/3.50  --clausify_out                          false
% 23.47/3.50  --sig_cnt_out                           false
% 23.47/3.50  --trig_cnt_out                          false
% 23.47/3.50  --trig_cnt_out_tolerance                1.
% 23.47/3.50  --trig_cnt_out_sk_spl                   false
% 23.47/3.50  --abstr_cl_out                          false
% 23.47/3.50  
% 23.47/3.50  ------ Global Options
% 23.47/3.50  
% 23.47/3.50  --schedule                              default
% 23.47/3.50  --add_important_lit                     false
% 23.47/3.50  --prop_solver_per_cl                    1000
% 23.47/3.50  --min_unsat_core                        false
% 23.47/3.50  --soft_assumptions                      false
% 23.47/3.50  --soft_lemma_size                       3
% 23.47/3.50  --prop_impl_unit_size                   0
% 23.47/3.50  --prop_impl_unit                        []
% 23.47/3.50  --share_sel_clauses                     true
% 23.47/3.50  --reset_solvers                         false
% 23.47/3.50  --bc_imp_inh                            [conj_cone]
% 23.47/3.50  --conj_cone_tolerance                   3.
% 23.47/3.50  --extra_neg_conj                        none
% 23.47/3.50  --large_theory_mode                     true
% 23.47/3.50  --prolific_symb_bound                   200
% 23.47/3.50  --lt_threshold                          2000
% 23.47/3.50  --clause_weak_htbl                      true
% 23.47/3.50  --gc_record_bc_elim                     false
% 23.47/3.50  
% 23.47/3.50  ------ Preprocessing Options
% 23.47/3.50  
% 23.47/3.50  --preprocessing_flag                    true
% 23.47/3.50  --time_out_prep_mult                    0.1
% 23.47/3.50  --splitting_mode                        input
% 23.47/3.50  --splitting_grd                         true
% 23.47/3.50  --splitting_cvd                         false
% 23.47/3.50  --splitting_cvd_svl                     false
% 23.47/3.50  --splitting_nvd                         32
% 23.47/3.50  --sub_typing                            true
% 23.47/3.50  --prep_gs_sim                           true
% 23.47/3.50  --prep_unflatten                        true
% 23.47/3.50  --prep_res_sim                          true
% 23.47/3.50  --prep_upred                            true
% 23.47/3.50  --prep_sem_filter                       exhaustive
% 23.47/3.50  --prep_sem_filter_out                   false
% 23.47/3.50  --pred_elim                             true
% 23.47/3.50  --res_sim_input                         true
% 23.47/3.50  --eq_ax_congr_red                       true
% 23.47/3.50  --pure_diseq_elim                       true
% 23.47/3.50  --brand_transform                       false
% 23.47/3.50  --non_eq_to_eq                          false
% 23.47/3.50  --prep_def_merge                        true
% 23.47/3.50  --prep_def_merge_prop_impl              false
% 23.47/3.50  --prep_def_merge_mbd                    true
% 23.47/3.50  --prep_def_merge_tr_red                 false
% 23.47/3.50  --prep_def_merge_tr_cl                  false
% 23.47/3.50  --smt_preprocessing                     true
% 23.47/3.50  --smt_ac_axioms                         fast
% 23.47/3.50  --preprocessed_out                      false
% 23.47/3.50  --preprocessed_stats                    false
% 23.47/3.50  
% 23.47/3.50  ------ Abstraction refinement Options
% 23.47/3.50  
% 23.47/3.50  --abstr_ref                             []
% 23.47/3.50  --abstr_ref_prep                        false
% 23.47/3.50  --abstr_ref_until_sat                   false
% 23.47/3.50  --abstr_ref_sig_restrict                funpre
% 23.47/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.47/3.50  --abstr_ref_under                       []
% 23.47/3.50  
% 23.47/3.50  ------ SAT Options
% 23.47/3.50  
% 23.47/3.50  --sat_mode                              false
% 23.47/3.50  --sat_fm_restart_options                ""
% 23.47/3.50  --sat_gr_def                            false
% 23.47/3.50  --sat_epr_types                         true
% 23.47/3.50  --sat_non_cyclic_types                  false
% 23.47/3.50  --sat_finite_models                     false
% 23.47/3.50  --sat_fm_lemmas                         false
% 23.47/3.50  --sat_fm_prep                           false
% 23.47/3.50  --sat_fm_uc_incr                        true
% 23.47/3.50  --sat_out_model                         small
% 23.47/3.50  --sat_out_clauses                       false
% 23.47/3.50  
% 23.47/3.50  ------ QBF Options
% 23.47/3.50  
% 23.47/3.50  --qbf_mode                              false
% 23.47/3.50  --qbf_elim_univ                         false
% 23.47/3.50  --qbf_dom_inst                          none
% 23.47/3.50  --qbf_dom_pre_inst                      false
% 23.47/3.50  --qbf_sk_in                             false
% 23.47/3.50  --qbf_pred_elim                         true
% 23.47/3.50  --qbf_split                             512
% 23.47/3.50  
% 23.47/3.50  ------ BMC1 Options
% 23.47/3.50  
% 23.47/3.50  --bmc1_incremental                      false
% 23.47/3.50  --bmc1_axioms                           reachable_all
% 23.47/3.50  --bmc1_min_bound                        0
% 23.47/3.50  --bmc1_max_bound                        -1
% 23.47/3.50  --bmc1_max_bound_default                -1
% 23.47/3.50  --bmc1_symbol_reachability              true
% 23.47/3.50  --bmc1_property_lemmas                  false
% 23.47/3.50  --bmc1_k_induction                      false
% 23.47/3.50  --bmc1_non_equiv_states                 false
% 23.47/3.50  --bmc1_deadlock                         false
% 23.47/3.50  --bmc1_ucm                              false
% 23.47/3.50  --bmc1_add_unsat_core                   none
% 23.47/3.50  --bmc1_unsat_core_children              false
% 23.47/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.47/3.50  --bmc1_out_stat                         full
% 23.47/3.50  --bmc1_ground_init                      false
% 23.47/3.50  --bmc1_pre_inst_next_state              false
% 23.47/3.50  --bmc1_pre_inst_state                   false
% 23.47/3.50  --bmc1_pre_inst_reach_state             false
% 23.47/3.50  --bmc1_out_unsat_core                   false
% 23.47/3.50  --bmc1_aig_witness_out                  false
% 23.47/3.50  --bmc1_verbose                          false
% 23.47/3.50  --bmc1_dump_clauses_tptp                false
% 23.47/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.47/3.50  --bmc1_dump_file                        -
% 23.47/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.47/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.47/3.50  --bmc1_ucm_extend_mode                  1
% 23.47/3.50  --bmc1_ucm_init_mode                    2
% 23.47/3.50  --bmc1_ucm_cone_mode                    none
% 23.47/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.47/3.50  --bmc1_ucm_relax_model                  4
% 23.47/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.47/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.47/3.50  --bmc1_ucm_layered_model                none
% 23.47/3.50  --bmc1_ucm_max_lemma_size               10
% 23.47/3.50  
% 23.47/3.50  ------ AIG Options
% 23.47/3.50  
% 23.47/3.50  --aig_mode                              false
% 23.47/3.50  
% 23.47/3.50  ------ Instantiation Options
% 23.47/3.50  
% 23.47/3.50  --instantiation_flag                    true
% 23.47/3.50  --inst_sos_flag                         true
% 23.47/3.50  --inst_sos_phase                        true
% 23.47/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.47/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.47/3.50  --inst_lit_sel_side                     none
% 23.47/3.50  --inst_solver_per_active                1400
% 23.47/3.50  --inst_solver_calls_frac                1.
% 23.47/3.50  --inst_passive_queue_type               priority_queues
% 23.47/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.47/3.50  --inst_passive_queues_freq              [25;2]
% 23.47/3.50  --inst_dismatching                      true
% 23.47/3.50  --inst_eager_unprocessed_to_passive     true
% 23.47/3.50  --inst_prop_sim_given                   true
% 23.47/3.50  --inst_prop_sim_new                     false
% 23.47/3.50  --inst_subs_new                         false
% 23.47/3.50  --inst_eq_res_simp                      false
% 23.47/3.50  --inst_subs_given                       false
% 23.47/3.50  --inst_orphan_elimination               true
% 23.47/3.50  --inst_learning_loop_flag               true
% 23.47/3.50  --inst_learning_start                   3000
% 23.47/3.50  --inst_learning_factor                  2
% 23.47/3.50  --inst_start_prop_sim_after_learn       3
% 23.47/3.50  --inst_sel_renew                        solver
% 23.47/3.50  --inst_lit_activity_flag                true
% 23.47/3.50  --inst_restr_to_given                   false
% 23.47/3.50  --inst_activity_threshold               500
% 23.47/3.50  --inst_out_proof                        true
% 23.47/3.50  
% 23.47/3.50  ------ Resolution Options
% 23.47/3.50  
% 23.47/3.50  --resolution_flag                       false
% 23.47/3.50  --res_lit_sel                           adaptive
% 23.47/3.50  --res_lit_sel_side                      none
% 23.47/3.50  --res_ordering                          kbo
% 23.47/3.50  --res_to_prop_solver                    active
% 23.47/3.50  --res_prop_simpl_new                    false
% 23.47/3.50  --res_prop_simpl_given                  true
% 23.47/3.50  --res_passive_queue_type                priority_queues
% 23.47/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.47/3.50  --res_passive_queues_freq               [15;5]
% 23.47/3.50  --res_forward_subs                      full
% 23.47/3.50  --res_backward_subs                     full
% 23.47/3.50  --res_forward_subs_resolution           true
% 23.47/3.50  --res_backward_subs_resolution          true
% 23.47/3.50  --res_orphan_elimination                true
% 23.47/3.50  --res_time_limit                        2.
% 23.47/3.50  --res_out_proof                         true
% 23.47/3.50  
% 23.47/3.50  ------ Superposition Options
% 23.47/3.50  
% 23.47/3.50  --superposition_flag                    true
% 23.47/3.50  --sup_passive_queue_type                priority_queues
% 23.47/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.47/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.47/3.50  --demod_completeness_check              fast
% 23.47/3.50  --demod_use_ground                      true
% 23.47/3.50  --sup_to_prop_solver                    passive
% 23.47/3.50  --sup_prop_simpl_new                    true
% 23.47/3.50  --sup_prop_simpl_given                  true
% 23.47/3.50  --sup_fun_splitting                     true
% 23.47/3.50  --sup_smt_interval                      50000
% 23.47/3.50  
% 23.47/3.50  ------ Superposition Simplification Setup
% 23.47/3.50  
% 23.47/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.47/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.47/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.47/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.47/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.47/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.47/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.47/3.50  --sup_immed_triv                        [TrivRules]
% 23.47/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.47/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.47/3.50  --sup_immed_bw_main                     []
% 23.47/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.47/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.47/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.47/3.50  --sup_input_bw                          []
% 23.47/3.50  
% 23.47/3.50  ------ Combination Options
% 23.47/3.50  
% 23.47/3.50  --comb_res_mult                         3
% 23.47/3.50  --comb_sup_mult                         2
% 23.47/3.50  --comb_inst_mult                        10
% 23.47/3.50  
% 23.47/3.50  ------ Debug Options
% 23.47/3.50  
% 23.47/3.50  --dbg_backtrace                         false
% 23.47/3.50  --dbg_dump_prop_clauses                 false
% 23.47/3.50  --dbg_dump_prop_clauses_file            -
% 23.47/3.50  --dbg_out_stat                          false
% 23.47/3.50  
% 23.47/3.50  
% 23.47/3.50  
% 23.47/3.50  
% 23.47/3.50  ------ Proving...
% 23.47/3.50  
% 23.47/3.50  
% 23.47/3.50  % SZS status Theorem for theBenchmark.p
% 23.47/3.50  
% 23.47/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.47/3.50  
% 23.47/3.50  fof(f18,conjecture,(
% 23.47/3.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f19,negated_conjecture,(
% 23.47/3.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 23.47/3.50    inference(negated_conjecture,[],[f18])).
% 23.47/3.50  
% 23.47/3.50  fof(f42,plain,(
% 23.47/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 23.47/3.50    inference(ennf_transformation,[],[f19])).
% 23.47/3.50  
% 23.47/3.50  fof(f43,plain,(
% 23.47/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 23.47/3.50    inference(flattening,[],[f42])).
% 23.47/3.50  
% 23.47/3.50  fof(f55,plain,(
% 23.47/3.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 23.47/3.50    introduced(choice_axiom,[])).
% 23.47/3.50  
% 23.47/3.50  fof(f54,plain,(
% 23.47/3.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 23.47/3.50    introduced(choice_axiom,[])).
% 23.47/3.50  
% 23.47/3.50  fof(f53,plain,(
% 23.47/3.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 23.47/3.50    introduced(choice_axiom,[])).
% 23.47/3.50  
% 23.47/3.50  fof(f52,plain,(
% 23.47/3.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 23.47/3.50    introduced(choice_axiom,[])).
% 23.47/3.50  
% 23.47/3.50  fof(f51,plain,(
% 23.47/3.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 23.47/3.50    introduced(choice_axiom,[])).
% 23.47/3.50  
% 23.47/3.50  fof(f50,plain,(
% 23.47/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 23.47/3.50    introduced(choice_axiom,[])).
% 23.47/3.50  
% 23.47/3.50  fof(f56,plain,(
% 23.47/3.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 23.47/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f43,f55,f54,f53,f52,f51,f50])).
% 23.47/3.50  
% 23.47/3.50  fof(f94,plain,(
% 23.47/3.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f13,axiom,(
% 23.47/3.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f32,plain,(
% 23.47/3.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 23.47/3.50    inference(ennf_transformation,[],[f13])).
% 23.47/3.50  
% 23.47/3.50  fof(f33,plain,(
% 23.47/3.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 23.47/3.50    inference(flattening,[],[f32])).
% 23.47/3.50  
% 23.47/3.50  fof(f72,plain,(
% 23.47/3.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f33])).
% 23.47/3.50  
% 23.47/3.50  fof(f12,axiom,(
% 23.47/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f20,plain,(
% 23.47/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 23.47/3.50    inference(pure_predicate_removal,[],[f12])).
% 23.47/3.50  
% 23.47/3.50  fof(f31,plain,(
% 23.47/3.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.47/3.50    inference(ennf_transformation,[],[f20])).
% 23.47/3.50  
% 23.47/3.50  fof(f70,plain,(
% 23.47/3.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.47/3.50    inference(cnf_transformation,[],[f31])).
% 23.47/3.50  
% 23.47/3.50  fof(f14,axiom,(
% 23.47/3.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f34,plain,(
% 23.47/3.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 23.47/3.50    inference(ennf_transformation,[],[f14])).
% 23.47/3.50  
% 23.47/3.50  fof(f35,plain,(
% 23.47/3.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.47/3.50    inference(flattening,[],[f34])).
% 23.47/3.50  
% 23.47/3.50  fof(f47,plain,(
% 23.47/3.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.47/3.50    inference(nnf_transformation,[],[f35])).
% 23.47/3.50  
% 23.47/3.50  fof(f73,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f47])).
% 23.47/3.50  
% 23.47/3.50  fof(f11,axiom,(
% 23.47/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f30,plain,(
% 23.47/3.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.47/3.50    inference(ennf_transformation,[],[f11])).
% 23.47/3.50  
% 23.47/3.50  fof(f69,plain,(
% 23.47/3.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.47/3.50    inference(cnf_transformation,[],[f30])).
% 23.47/3.50  
% 23.47/3.50  fof(f83,plain,(
% 23.47/3.50    ~v1_xboole_0(sK1)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f92,plain,(
% 23.47/3.50    v1_funct_1(sK5)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f93,plain,(
% 23.47/3.50    v1_funct_2(sK5,sK3,sK1)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f3,axiom,(
% 23.47/3.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f60,plain,(
% 23.47/3.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 23.47/3.50    inference(cnf_transformation,[],[f3])).
% 23.47/3.50  
% 23.47/3.50  fof(f7,axiom,(
% 23.47/3.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f24,plain,(
% 23.47/3.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 23.47/3.50    inference(ennf_transformation,[],[f7])).
% 23.47/3.50  
% 23.47/3.50  fof(f25,plain,(
% 23.47/3.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.47/3.50    inference(flattening,[],[f24])).
% 23.47/3.50  
% 23.47/3.50  fof(f63,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f25])).
% 23.47/3.50  
% 23.47/3.50  fof(f9,axiom,(
% 23.47/3.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f27,plain,(
% 23.47/3.50    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.47/3.50    inference(ennf_transformation,[],[f9])).
% 23.47/3.50  
% 23.47/3.50  fof(f45,plain,(
% 23.47/3.50    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.47/3.50    inference(nnf_transformation,[],[f27])).
% 23.47/3.50  
% 23.47/3.50  fof(f65,plain,(
% 23.47/3.50    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f45])).
% 23.47/3.50  
% 23.47/3.50  fof(f6,axiom,(
% 23.47/3.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f23,plain,(
% 23.47/3.50    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 23.47/3.50    inference(ennf_transformation,[],[f6])).
% 23.47/3.50  
% 23.47/3.50  fof(f62,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f23])).
% 23.47/3.50  
% 23.47/3.50  fof(f1,axiom,(
% 23.47/3.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f44,plain,(
% 23.47/3.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 23.47/3.50    inference(nnf_transformation,[],[f1])).
% 23.47/3.50  
% 23.47/3.50  fof(f57,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f44])).
% 23.47/3.50  
% 23.47/3.50  fof(f4,axiom,(
% 23.47/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f61,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 23.47/3.50    inference(cnf_transformation,[],[f4])).
% 23.47/3.50  
% 23.47/3.50  fof(f97,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 23.47/3.50    inference(definition_unfolding,[],[f57,f61])).
% 23.47/3.50  
% 23.47/3.50  fof(f8,axiom,(
% 23.47/3.50    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f26,plain,(
% 23.47/3.50    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 23.47/3.50    inference(ennf_transformation,[],[f8])).
% 23.47/3.50  
% 23.47/3.50  fof(f64,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f26])).
% 23.47/3.50  
% 23.47/3.50  fof(f99,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 23.47/3.50    inference(definition_unfolding,[],[f64,f61])).
% 23.47/3.50  
% 23.47/3.50  fof(f66,plain,(
% 23.47/3.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f45])).
% 23.47/3.50  
% 23.47/3.50  fof(f91,plain,(
% 23.47/3.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f15,axiom,(
% 23.47/3.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f36,plain,(
% 23.47/3.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 23.47/3.50    inference(ennf_transformation,[],[f15])).
% 23.47/3.50  
% 23.47/3.50  fof(f37,plain,(
% 23.47/3.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 23.47/3.50    inference(flattening,[],[f36])).
% 23.47/3.50  
% 23.47/3.50  fof(f75,plain,(
% 23.47/3.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f37])).
% 23.47/3.50  
% 23.47/3.50  fof(f10,axiom,(
% 23.47/3.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f28,plain,(
% 23.47/3.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 23.47/3.50    inference(ennf_transformation,[],[f10])).
% 23.47/3.50  
% 23.47/3.50  fof(f29,plain,(
% 23.47/3.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 23.47/3.50    inference(flattening,[],[f28])).
% 23.47/3.50  
% 23.47/3.50  fof(f46,plain,(
% 23.47/3.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 23.47/3.50    inference(nnf_transformation,[],[f29])).
% 23.47/3.50  
% 23.47/3.50  fof(f67,plain,(
% 23.47/3.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f46])).
% 23.47/3.50  
% 23.47/3.50  fof(f88,plain,(
% 23.47/3.50    r1_subset_1(sK2,sK3)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f84,plain,(
% 23.47/3.50    ~v1_xboole_0(sK2)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f86,plain,(
% 23.47/3.50    ~v1_xboole_0(sK3)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f87,plain,(
% 23.47/3.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f2,axiom,(
% 23.47/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f22,plain,(
% 23.47/3.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 23.47/3.50    inference(ennf_transformation,[],[f2])).
% 23.47/3.50  
% 23.47/3.50  fof(f59,plain,(
% 23.47/3.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 23.47/3.50    inference(cnf_transformation,[],[f22])).
% 23.47/3.50  
% 23.47/3.50  fof(f98,plain,(
% 23.47/3.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 23.47/3.50    inference(definition_unfolding,[],[f59,f61])).
% 23.47/3.50  
% 23.47/3.50  fof(f95,plain,(
% 23.47/3.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f89,plain,(
% 23.47/3.50    v1_funct_1(sK4)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f82,plain,(
% 23.47/3.50    ~v1_xboole_0(sK0)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f85,plain,(
% 23.47/3.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f16,axiom,(
% 23.47/3.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f38,plain,(
% 23.47/3.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 23.47/3.50    inference(ennf_transformation,[],[f16])).
% 23.47/3.50  
% 23.47/3.50  fof(f39,plain,(
% 23.47/3.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 23.47/3.50    inference(flattening,[],[f38])).
% 23.47/3.50  
% 23.47/3.50  fof(f48,plain,(
% 23.47/3.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 23.47/3.50    inference(nnf_transformation,[],[f39])).
% 23.47/3.50  
% 23.47/3.50  fof(f49,plain,(
% 23.47/3.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 23.47/3.50    inference(flattening,[],[f48])).
% 23.47/3.50  
% 23.47/3.50  fof(f77,plain,(
% 23.47/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f49])).
% 23.47/3.50  
% 23.47/3.50  fof(f103,plain,(
% 23.47/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.47/3.50    inference(equality_resolution,[],[f77])).
% 23.47/3.50  
% 23.47/3.50  fof(f17,axiom,(
% 23.47/3.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 23.47/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.47/3.50  
% 23.47/3.50  fof(f40,plain,(
% 23.47/3.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 23.47/3.50    inference(ennf_transformation,[],[f17])).
% 23.47/3.50  
% 23.47/3.50  fof(f41,plain,(
% 23.47/3.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 23.47/3.50    inference(flattening,[],[f40])).
% 23.47/3.50  
% 23.47/3.50  fof(f79,plain,(
% 23.47/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f41])).
% 23.47/3.50  
% 23.47/3.50  fof(f80,plain,(
% 23.47/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f41])).
% 23.47/3.50  
% 23.47/3.50  fof(f81,plain,(
% 23.47/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f41])).
% 23.47/3.50  
% 23.47/3.50  fof(f90,plain,(
% 23.47/3.50    v1_funct_2(sK4,sK2,sK1)),
% 23.47/3.50    inference(cnf_transformation,[],[f56])).
% 23.47/3.50  
% 23.47/3.50  fof(f76,plain,(
% 23.47/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.47/3.50    inference(cnf_transformation,[],[f49])).
% 23.47/3.50  
% 23.47/3.50  fof(f104,plain,(
% 23.47/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.47/3.50    inference(equality_resolution,[],[f76])).
% 23.47/3.50  
% 23.47/3.50  cnf(c_25,negated_conjecture,
% 23.47/3.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 23.47/3.50      inference(cnf_transformation,[],[f94]) ).
% 23.47/3.50  
% 23.47/3.50  cnf(c_1247,negated_conjecture,
% 23.47/3.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 23.47/3.50      inference(subtyping,[status(esa)],[c_25]) ).
% 23.47/3.50  
% 23.47/3.50  cnf(c_2043,plain,
% 23.47/3.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 23.47/3.50      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 23.47/3.50  
% 23.47/3.50  cnf(c_13,plain,
% 23.47/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.50      | v1_partfun1(X0,X1)
% 23.47/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.50      | ~ v1_funct_1(X0)
% 23.47/3.50      | v1_xboole_0(X2) ),
% 23.47/3.50      inference(cnf_transformation,[],[f72]) ).
% 23.47/3.50  
% 23.47/3.50  cnf(c_12,plain,
% 23.47/3.50      ( v4_relat_1(X0,X1)
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 23.47/3.51      inference(cnf_transformation,[],[f70]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_16,plain,
% 23.47/3.51      ( ~ v1_partfun1(X0,X1)
% 23.47/3.51      | ~ v4_relat_1(X0,X1)
% 23.47/3.51      | ~ v1_relat_1(X0)
% 23.47/3.51      | k1_relat_1(X0) = X1 ),
% 23.47/3.51      inference(cnf_transformation,[],[f73]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_505,plain,
% 23.47/3.51      ( ~ v1_partfun1(X0,X1)
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ v1_relat_1(X0)
% 23.47/3.51      | k1_relat_1(X0) = X1 ),
% 23.47/3.51      inference(resolution,[status(thm)],[c_12,c_16]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_11,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | v1_relat_1(X0) ),
% 23.47/3.51      inference(cnf_transformation,[],[f69]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_509,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ v1_partfun1(X0,X1)
% 23.47/3.51      | k1_relat_1(X0) = X1 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_505,c_16,c_12,c_11]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_510,plain,
% 23.47/3.51      ( ~ v1_partfun1(X0,X1)
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | k1_relat_1(X0) = X1 ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_509]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_569,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | k1_relat_1(X0) = X1 ),
% 23.47/3.51      inference(resolution,[status(thm)],[c_13,c_510]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_573,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | k1_relat_1(X0) = X1 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_569,c_16,c_13,c_12,c_11]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_574,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | k1_relat_1(X0) = X1 ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_573]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1231,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 23.47/3.51      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 23.47/3.51      | ~ v1_funct_1(X0_54)
% 23.47/3.51      | v1_xboole_0(X2_54)
% 23.47/3.51      | k1_relat_1(X0_54) = X1_54 ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_574]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2059,plain,
% 23.47/3.51      ( k1_relat_1(X0_54) = X1_54
% 23.47/3.51      | v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 23.47/3.51      | v1_funct_1(X0_54) != iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1231]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7076,plain,
% 23.47/3.51      ( k1_relat_1(sK5) = sK3
% 23.47/3.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 23.47/3.51      | v1_funct_1(sK5) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK1) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2043,c_2059]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_36,negated_conjecture,
% 23.47/3.51      ( ~ v1_xboole_0(sK1) ),
% 23.47/3.51      inference(cnf_transformation,[],[f83]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_27,negated_conjecture,
% 23.47/3.51      ( v1_funct_1(sK5) ),
% 23.47/3.51      inference(cnf_transformation,[],[f92]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_26,negated_conjecture,
% 23.47/3.51      ( v1_funct_2(sK5,sK3,sK1) ),
% 23.47/3.51      inference(cnf_transformation,[],[f93]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2146,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0_54,X1_54,sK1)
% 23.47/3.51      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1)))
% 23.47/3.51      | ~ v1_funct_1(X0_54)
% 23.47/3.51      | v1_xboole_0(sK1)
% 23.47/3.51      | k1_relat_1(X0_54) = X1_54 ),
% 23.47/3.51      inference(instantiation,[status(thm)],[c_1231]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2283,plain,
% 23.47/3.51      ( ~ v1_funct_2(sK5,X0_54,sK1)
% 23.47/3.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1)))
% 23.47/3.51      | ~ v1_funct_1(sK5)
% 23.47/3.51      | v1_xboole_0(sK1)
% 23.47/3.51      | k1_relat_1(sK5) = X0_54 ),
% 23.47/3.51      inference(instantiation,[status(thm)],[c_2146]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2343,plain,
% 23.47/3.51      ( ~ v1_funct_2(sK5,sK3,sK1)
% 23.47/3.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 23.47/3.51      | ~ v1_funct_1(sK5)
% 23.47/3.51      | v1_xboole_0(sK1)
% 23.47/3.51      | k1_relat_1(sK5) = sK3 ),
% 23.47/3.51      inference(instantiation,[status(thm)],[c_2283]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7115,plain,
% 23.47/3.51      ( k1_relat_1(sK5) = sK3 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_7076,c_36,c_27,c_26,c_25,c_2343]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1254,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 23.47/3.51      | v1_relat_1(X0_54) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_11]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2037,plain,
% 23.47/3.51      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 23.47/3.51      | v1_relat_1(X0_54) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3167,plain,
% 23.47/3.51      ( v1_relat_1(sK5) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2043,c_2037]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3,plain,
% 23.47/3.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 23.47/3.51      inference(cnf_transformation,[],[f60]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1259,plain,
% 23.47/3.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_3]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2032,plain,
% 23.47/3.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1259]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5,plain,
% 23.47/3.51      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 23.47/3.51      inference(cnf_transformation,[],[f63]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_525,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ v1_relat_1(X0)
% 23.47/3.51      | k7_relat_1(X0,X1) = X0 ),
% 23.47/3.51      inference(resolution,[status(thm)],[c_12,c_5]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_529,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | k7_relat_1(X0,X1) = X0 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_525,c_12,c_11,c_5]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1232,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 23.47/3.51      | k7_relat_1(X0_54,X1_54) = X0_54 ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_529]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2058,plain,
% 23.47/3.51      ( k7_relat_1(X0_54,X1_54) = X0_54
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4251,plain,
% 23.47/3.51      ( k7_relat_1(k1_xboole_0,X0_54) = k1_xboole_0 ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2032,c_2058]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_8,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(X0),X1)
% 23.47/3.51      | ~ v1_relat_1(X0)
% 23.47/3.51      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 23.47/3.51      inference(cnf_transformation,[],[f65]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1255,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(X0_54),X1_54)
% 23.47/3.51      | ~ v1_relat_1(X0_54)
% 23.47/3.51      | k7_relat_1(X0_54,X1_54) != k1_xboole_0 ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_8]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2036,plain,
% 23.47/3.51      ( k7_relat_1(X0_54,X1_54) != k1_xboole_0
% 23.47/3.51      | r1_xboole_0(k1_relat_1(X0_54),X1_54) = iProver_top
% 23.47/3.51      | v1_relat_1(X0_54) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1255]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4419,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0_54) = iProver_top
% 23.47/3.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_4251,c_2036]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3169,plain,
% 23.47/3.51      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2032,c_2037]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4831,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0_54) = iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_4419,c_3169]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4,plain,
% 23.47/3.51      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 23.47/3.51      | ~ v1_relat_1(X1)
% 23.47/3.51      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 23.47/3.51      inference(cnf_transformation,[],[f62]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1258,plain,
% 23.47/3.51      ( ~ r1_xboole_0(X0_54,k1_relat_1(X1_54))
% 23.47/3.51      | ~ v1_relat_1(X1_54)
% 23.47/3.51      | k7_relat_1(X1_54,X0_54) = k1_xboole_0 ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_4]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2033,plain,
% 23.47/3.51      ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 23.47/3.51      | r1_xboole_0(X1_54,k1_relat_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_relat_1(X0_54) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4839,plain,
% 23.47/3.51      ( k7_relat_1(X0_54,k1_relat_1(k1_xboole_0)) = k1_xboole_0
% 23.47/3.51      | v1_relat_1(X0_54) != iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_4831,c_2033]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4945,plain,
% 23.47/3.51      ( k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_3167,c_4839]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4998,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(k1_xboole_0)) = iProver_top
% 23.47/3.51      | v1_relat_1(sK5) != iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_4945,c_2036]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6734,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_4998,c_3167]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7117,plain,
% 23.47/3.51      ( r1_xboole_0(sK3,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_7115,c_6734]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1,plain,
% 23.47/3.51      ( ~ r1_xboole_0(X0,X1)
% 23.47/3.51      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 23.47/3.51      inference(cnf_transformation,[],[f97]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1261,plain,
% 23.47/3.51      ( ~ r1_xboole_0(X0_54,X1_54)
% 23.47/3.51      | k1_setfam_1(k2_tarski(X0_54,X1_54)) = k1_xboole_0 ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_1]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2030,plain,
% 23.47/3.51      ( k1_setfam_1(k2_tarski(X0_54,X1_54)) = k1_xboole_0
% 23.47/3.51      | r1_xboole_0(X0_54,X1_54) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6739,plain,
% 23.47/3.51      ( k1_setfam_1(k2_tarski(k1_relat_1(sK5),k1_relat_1(k1_xboole_0))) = k1_xboole_0 ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_6734,c_2030]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6,plain,
% 23.47/3.51      ( ~ v1_relat_1(X0)
% 23.47/3.51      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 23.47/3.51      inference(cnf_transformation,[],[f99]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1257,plain,
% 23.47/3.51      ( ~ v1_relat_1(X0_54)
% 23.47/3.51      | k1_setfam_1(k2_tarski(k1_relat_1(X0_54),X1_54)) = k1_relat_1(k7_relat_1(X0_54,X1_54)) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_6]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2034,plain,
% 23.47/3.51      ( k1_setfam_1(k2_tarski(k1_relat_1(X0_54),X1_54)) = k1_relat_1(k7_relat_1(X0_54,X1_54))
% 23.47/3.51      | v1_relat_1(X0_54) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3799,plain,
% 23.47/3.51      ( k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_54)) = k1_relat_1(k7_relat_1(sK5,X0_54)) ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_3167,c_2034]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6744,plain,
% 23.47/3.51      ( k1_relat_1(k7_relat_1(sK5,k1_relat_1(k1_xboole_0))) = k1_xboole_0 ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_6739,c_3799]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6745,plain,
% 23.47/3.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 23.47/3.51      inference(light_normalisation,[status(thm)],[c_6744,c_4945]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7127,plain,
% 23.47/3.51      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 23.47/3.51      inference(light_normalisation,[status(thm)],[c_7117,c_6745]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7,plain,
% 23.47/3.51      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 23.47/3.51      | ~ v1_relat_1(X0)
% 23.47/3.51      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 23.47/3.51      inference(cnf_transformation,[],[f66]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1256,plain,
% 23.47/3.51      ( ~ r1_xboole_0(k1_relat_1(X0_54),X1_54)
% 23.47/3.51      | ~ v1_relat_1(X0_54)
% 23.47/3.51      | k7_relat_1(X0_54,X1_54) = k1_xboole_0 ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_7]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2035,plain,
% 23.47/3.51      ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 23.47/3.51      | r1_xboole_0(k1_relat_1(X0_54),X1_54) != iProver_top
% 23.47/3.51      | v1_relat_1(X0_54) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7135,plain,
% 23.47/3.51      ( k7_relat_1(sK5,X0_54) = k1_xboole_0
% 23.47/3.51      | r1_xboole_0(sK3,X0_54) != iProver_top
% 23.47/3.51      | v1_relat_1(sK5) != iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_7115,c_2035]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7144,plain,
% 23.47/3.51      ( r1_xboole_0(sK3,X0_54) != iProver_top
% 23.47/3.51      | k7_relat_1(sK5,X0_54) = k1_xboole_0 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_7135,c_3167]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7145,plain,
% 23.47/3.51      ( k7_relat_1(sK5,X0_54) = k1_xboole_0
% 23.47/3.51      | r1_xboole_0(sK3,X0_54) != iProver_top ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_7144]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_35864,plain,
% 23.47/3.51      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_7127,c_7145]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_28,negated_conjecture,
% 23.47/3.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 23.47/3.51      inference(cnf_transformation,[],[f91]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1244,negated_conjecture,
% 23.47/3.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_28]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2046,plain,
% 23.47/3.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3168,plain,
% 23.47/3.51      ( v1_relat_1(sK4) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2046,c_2037]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4946,plain,
% 23.47/3.51      ( k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_3168,c_4839]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5594,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(sK4),k1_relat_1(k1_xboole_0)) = iProver_top
% 23.47/3.51      | v1_relat_1(sK4) != iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_4946,c_2036]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6791,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(sK4),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_5594,c_3168]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6795,plain,
% 23.47/3.51      ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) = iProver_top ),
% 23.47/3.51      inference(light_normalisation,[status(thm)],[c_6791,c_6745]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6797,plain,
% 23.47/3.51      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0
% 23.47/3.51      | v1_relat_1(sK4) != iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_6795,c_2035]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7090,plain,
% 23.47/3.51      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_6797,c_3168]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_17,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 23.47/3.51      inference(cnf_transformation,[],[f75]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1253,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 23.47/3.51      | ~ v1_funct_1(X0_54)
% 23.47/3.51      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_17]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2038,plain,
% 23.47/3.51      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 23.47/3.51      | v1_funct_1(X2_54) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1253]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3954,plain,
% 23.47/3.51      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
% 23.47/3.51      | v1_funct_1(sK5) != iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2043,c_2038]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_48,plain,
% 23.47/3.51      ( v1_funct_1(sK5) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4071,plain,
% 23.47/3.51      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_3954,c_48]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_10,plain,
% 23.47/3.51      ( ~ r1_subset_1(X0,X1)
% 23.47/3.51      | r1_xboole_0(X0,X1)
% 23.47/3.51      | v1_xboole_0(X0)
% 23.47/3.51      | v1_xboole_0(X1) ),
% 23.47/3.51      inference(cnf_transformation,[],[f67]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_31,negated_conjecture,
% 23.47/3.51      ( r1_subset_1(sK2,sK3) ),
% 23.47/3.51      inference(cnf_transformation,[],[f88]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_492,plain,
% 23.47/3.51      ( r1_xboole_0(X0,X1)
% 23.47/3.51      | v1_xboole_0(X0)
% 23.47/3.51      | v1_xboole_0(X1)
% 23.47/3.51      | sK3 != X1
% 23.47/3.51      | sK2 != X0 ),
% 23.47/3.51      inference(resolution_lifted,[status(thm)],[c_10,c_31]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_493,plain,
% 23.47/3.51      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 23.47/3.51      inference(unflattening,[status(thm)],[c_492]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_35,negated_conjecture,
% 23.47/3.51      ( ~ v1_xboole_0(sK2) ),
% 23.47/3.51      inference(cnf_transformation,[],[f84]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_33,negated_conjecture,
% 23.47/3.51      ( ~ v1_xboole_0(sK3) ),
% 23.47/3.51      inference(cnf_transformation,[],[f86]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_495,plain,
% 23.47/3.51      ( r1_xboole_0(sK2,sK3) ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_493,c_35,c_33]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1233,plain,
% 23.47/3.51      ( r1_xboole_0(sK2,sK3) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_495]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2057,plain,
% 23.47/3.51      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3235,plain,
% 23.47/3.51      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2057,c_2030]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_32,negated_conjecture,
% 23.47/3.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 23.47/3.51      inference(cnf_transformation,[],[f87]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1241,negated_conjecture,
% 23.47/3.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_32]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2049,plain,
% 23.47/3.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.47/3.51      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 23.47/3.51      inference(cnf_transformation,[],[f98]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1260,plain,
% 23.47/3.51      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 23.47/3.51      | k9_subset_1(X1_54,X2_54,X0_54) = k1_setfam_1(k2_tarski(X2_54,X0_54)) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_2]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2031,plain,
% 23.47/3.51      ( k9_subset_1(X0_54,X1_54,X2_54) = k1_setfam_1(k2_tarski(X1_54,X2_54))
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1260]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2750,plain,
% 23.47/3.51      ( k9_subset_1(sK0,X0_54,sK3) = k1_setfam_1(k2_tarski(X0_54,sK3)) ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2049,c_2031]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_24,negated_conjecture,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 23.47/3.51      inference(cnf_transformation,[],[f95]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1248,negated_conjecture,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_24]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3000,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_2750,c_1248]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3818,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_3235,c_3000]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4074,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_4071,c_3818]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_3955,plain,
% 23.47/3.51      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 23.47/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2046,c_2038]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_30,negated_conjecture,
% 23.47/3.51      ( v1_funct_1(sK4) ),
% 23.47/3.51      inference(cnf_transformation,[],[f89]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_45,plain,
% 23.47/3.51      ( v1_funct_1(sK4) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4096,plain,
% 23.47/3.51      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_3955,c_45]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4099,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_4074,c_4096]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_7092,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_7090,c_4099]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_37,negated_conjecture,
% 23.47/3.51      ( ~ v1_xboole_0(sK0) ),
% 23.47/3.51      inference(cnf_transformation,[],[f82]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_34,negated_conjecture,
% 23.47/3.51      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 23.47/3.51      inference(cnf_transformation,[],[f85]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_19,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_1(X3)
% 23.47/3.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X1)
% 23.47/3.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 23.47/3.51      inference(cnf_transformation,[],[f103]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_23,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_1(X3)
% 23.47/3.51      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X1) ),
% 23.47/3.51      inference(cnf_transformation,[],[f79]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_22,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_1(X3)
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X1) ),
% 23.47/3.51      inference(cnf_transformation,[],[f80]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_21,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_1(X3)
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X1) ),
% 23.47/3.51      inference(cnf_transformation,[],[f81]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_217,plain,
% 23.47/3.51      ( ~ v1_funct_1(X3)
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X1)
% 23.47/3.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_19,c_23,c_22,c_21]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_218,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_1(X3)
% 23.47/3.51      | v1_xboole_0(X1)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_217]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1234,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 23.47/3.51      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 23.47/3.51      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 23.47/3.51      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 23.47/3.51      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 23.47/3.51      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 23.47/3.51      | ~ v1_funct_1(X0_54)
% 23.47/3.51      | ~ v1_funct_1(X3_54)
% 23.47/3.51      | v1_xboole_0(X2_54)
% 23.47/3.51      | v1_xboole_0(X1_54)
% 23.47/3.51      | v1_xboole_0(X4_54)
% 23.47/3.51      | v1_xboole_0(X5_54)
% 23.47/3.51      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_218]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2056,plain,
% 23.47/3.51      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 23.47/3.51      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 23.47/3.51      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 23.47/3.51      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 23.47/3.51      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 23.47/3.51      | v1_funct_1(X2_54) != iProver_top
% 23.47/3.51      | v1_funct_1(X5_54) != iProver_top
% 23.47/3.51      | v1_xboole_0(X3_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X4_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1234]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_6000,plain,
% 23.47/3.51      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 23.47/3.51      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 23.47/3.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(X1_54) != iProver_top
% 23.47/3.51      | v1_funct_1(sK5) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK1) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK3) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_4071,c_2056]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_39,plain,
% 23.47/3.51      ( v1_xboole_0(sK1) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_42,plain,
% 23.47/3.51      ( v1_xboole_0(sK3) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_49,plain,
% 23.47/3.51      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_50,plain,
% 23.47/3.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_15330,plain,
% 23.47/3.51      ( v1_funct_1(X1_54) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 23.47/3.51      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 23.47/3.51      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_6000,c_39,c_42,c_48,c_49,c_50]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_15331,plain,
% 23.47/3.51      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 23.47/3.51      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(X1_54) != iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_15330]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_15337,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 23.47/3.51      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 23.47/3.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(sK4) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK2) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_4096,c_15331]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_40,plain,
% 23.47/3.51      ( v1_xboole_0(sK2) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_29,negated_conjecture,
% 23.47/3.51      ( v1_funct_2(sK4,sK2,sK1) ),
% 23.47/3.51      inference(cnf_transformation,[],[f90]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_46,plain,
% 23.47/3.51      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_47,plain,
% 23.47/3.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_16850,plain,
% 23.47/3.51      ( v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 23.47/3.51      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_15337,c_40,c_45,c_46,c_47]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_16851,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 23.47/3.51      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_16850]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_16856,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 23.47/3.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2750,c_16851]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_16857,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 23.47/3.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(light_normalisation,[status(thm)],[c_16856,c_3235]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_16858,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 23.47/3.51      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_16857,c_2750]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_16859,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 23.47/3.51      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(light_normalisation,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_16858,c_3235,c_7090]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_16860,plain,
% 23.47/3.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 23.47/3.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 23.47/3.51      | v1_xboole_0(sK0)
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 23.47/3.51      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 23.47/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_16859]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_34063,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_7092,c_37,c_34,c_32,c_16860]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1249,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 23.47/3.51      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 23.47/3.51      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 23.47/3.51      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 23.47/3.51      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 23.47/3.51      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 23.47/3.51      | ~ v1_funct_1(X0_54)
% 23.47/3.51      | ~ v1_funct_1(X3_54)
% 23.47/3.51      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
% 23.47/3.51      | v1_xboole_0(X2_54)
% 23.47/3.51      | v1_xboole_0(X1_54)
% 23.47/3.51      | v1_xboole_0(X4_54)
% 23.47/3.51      | v1_xboole_0(X5_54) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_23]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2042,plain,
% 23.47/3.51      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 23.47/3.51      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 23.47/3.51      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 23.47/3.51      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 23.47/3.51      | v1_funct_1(X0_54) != iProver_top
% 23.47/3.51      | v1_funct_1(X3_54) != iProver_top
% 23.47/3.51      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
% 23.47/3.51      | v1_xboole_0(X5_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X4_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1251,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 23.47/3.51      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 23.47/3.51      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 23.47/3.51      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 23.47/3.51      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 23.47/3.51      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 23.47/3.51      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
% 23.47/3.51      | ~ v1_funct_1(X0_54)
% 23.47/3.51      | ~ v1_funct_1(X3_54)
% 23.47/3.51      | v1_xboole_0(X2_54)
% 23.47/3.51      | v1_xboole_0(X1_54)
% 23.47/3.51      | v1_xboole_0(X4_54)
% 23.47/3.51      | v1_xboole_0(X5_54) ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_21]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2040,plain,
% 23.47/3.51      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 23.47/3.51      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 23.47/3.51      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 23.47/3.51      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 23.47/3.51      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
% 23.47/3.51      | v1_funct_1(X0_54) != iProver_top
% 23.47/3.51      | v1_funct_1(X3_54) != iProver_top
% 23.47/3.51      | v1_xboole_0(X5_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X4_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1251]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4355,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 23.47/3.51      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 23.47/3.51      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 23.47/3.51      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 23.47/3.51      | v1_funct_1(X5_54) != iProver_top
% 23.47/3.51      | v1_funct_1(X4_54) != iProver_top
% 23.47/3.51      | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X3_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2040,c_2038]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_11470,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 23.47/3.51      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 23.47/3.51      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 23.47/3.51      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 23.47/3.51      | v1_funct_1(X5_54) != iProver_top
% 23.47/3.51      | v1_funct_1(X4_54) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X3_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2042,c_4355]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_18566,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 23.47/3.51      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 23.47/3.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(X2_54) != iProver_top
% 23.47/3.51      | v1_funct_1(sK5) != iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK1) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK3) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2043,c_11470]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_18583,plain,
% 23.47/3.51      ( v1_funct_1(X2_54) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 23.47/3.51      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_18566,c_39,c_42,c_48,c_49]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_18584,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 23.47/3.51      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(X2_54) != iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_18583]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_18590,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 23.47/3.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(sK4) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK2) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2046,c_18584]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_19043,plain,
% 23.47/3.51      ( v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_18590,c_40,c_45,c_46]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_19044,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_19043]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_19049,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54)
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2049,c_19044]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_38,plain,
% 23.47/3.51      ( v1_xboole_0(sK0) != iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_41,plain,
% 23.47/3.51      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_19054,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_19049,c_38,c_41]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_34065,plain,
% 23.47/3.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 23.47/3.51      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_34063,c_19054]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_20,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_1(X3)
% 23.47/3.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X1)
% 23.47/3.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 23.47/3.51      inference(cnf_transformation,[],[f104]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_210,plain,
% 23.47/3.51      ( ~ v1_funct_1(X3)
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X1)
% 23.47/3.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_20,c_23,c_22,c_21]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_211,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0,X1,X2)
% 23.47/3.51      | ~ v1_funct_2(X3,X4,X2)
% 23.47/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 23.47/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.47/3.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.47/3.51      | ~ v1_funct_1(X0)
% 23.47/3.51      | ~ v1_funct_1(X3)
% 23.47/3.51      | v1_xboole_0(X1)
% 23.47/3.51      | v1_xboole_0(X2)
% 23.47/3.51      | v1_xboole_0(X4)
% 23.47/3.51      | v1_xboole_0(X5)
% 23.47/3.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_210]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_1235,plain,
% 23.47/3.51      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 23.47/3.51      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 23.47/3.51      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 23.47/3.51      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 23.47/3.51      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 23.47/3.51      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 23.47/3.51      | ~ v1_funct_1(X0_54)
% 23.47/3.51      | ~ v1_funct_1(X3_54)
% 23.47/3.51      | v1_xboole_0(X2_54)
% 23.47/3.51      | v1_xboole_0(X1_54)
% 23.47/3.51      | v1_xboole_0(X4_54)
% 23.47/3.51      | v1_xboole_0(X5_54)
% 23.47/3.51      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 23.47/3.51      inference(subtyping,[status(esa)],[c_211]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_2055,plain,
% 23.47/3.51      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 23.47/3.51      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 23.47/3.51      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 23.47/3.51      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 23.47/3.51      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 23.47/3.51      | v1_funct_1(X2_54) != iProver_top
% 23.47/3.51      | v1_funct_1(X5_54) != iProver_top
% 23.47/3.51      | v1_xboole_0(X3_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X1_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X4_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(predicate_to_equality,[status(thm)],[c_1235]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_4775,plain,
% 23.47/3.51      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 23.47/3.51      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 23.47/3.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(X1_54) != iProver_top
% 23.47/3.51      | v1_funct_1(sK5) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK1) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK3) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_4071,c_2055]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5599,plain,
% 23.47/3.51      ( v1_funct_1(X1_54) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 23.47/3.51      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 23.47/3.51      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_4775,c_39,c_42,c_48,c_49,c_50]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5600,plain,
% 23.47/3.51      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 23.47/3.51      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 23.47/3.51      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(X1_54) != iProver_top
% 23.47/3.51      | v1_xboole_0(X2_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_5599]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5606,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 23.47/3.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 23.47/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_funct_1(sK4) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | v1_xboole_0(sK2) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_4096,c_5600]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5712,plain,
% 23.47/3.51      ( v1_xboole_0(X0_54) = iProver_top
% 23.47/3.51      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_5606,c_40,c_45,c_46,c_47]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5713,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 23.47/3.51      | v1_xboole_0(X0_54) = iProver_top ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_5712]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5718,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(superposition,[status(thm)],[c_2750,c_5713]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5719,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(light_normalisation,[status(thm)],[c_5718,c_3235]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5720,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_5719,c_2750]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5721,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 23.47/3.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 23.47/3.51      | v1_xboole_0(sK0) = iProver_top ),
% 23.47/3.51      inference(light_normalisation,[status(thm)],[c_5720,c_3235]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_5722,plain,
% 23.47/3.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 23.47/3.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 23.47/3.51      | v1_xboole_0(sK0)
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 23.47/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_5721]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_25274,plain,
% 23.47/3.51      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 23.47/3.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_5721,c_37,c_34,c_32,c_5722]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_25275,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 23.47/3.51      inference(renaming,[status(thm)],[c_25274]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_25276,plain,
% 23.47/3.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 23.47/3.51      inference(light_normalisation,[status(thm)],[c_25275,c_7090]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_25277,plain,
% 23.47/3.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 23.47/3.51      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 23.47/3.51      inference(demodulation,[status(thm)],[c_25276,c_19054]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(c_34066,plain,
% 23.47/3.51      ( k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 23.47/3.51      inference(global_propositional_subsumption,
% 23.47/3.51                [status(thm)],
% 23.47/3.51                [c_34065,c_25277]) ).
% 23.47/3.51  
% 23.47/3.51  cnf(contradiction,plain,
% 23.47/3.51      ( $false ),
% 23.47/3.51      inference(minisat,[status(thm)],[c_35864,c_34066]) ).
% 23.47/3.51  
% 23.47/3.51  
% 23.47/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.47/3.51  
% 23.47/3.51  ------                               Statistics
% 23.47/3.51  
% 23.47/3.51  ------ General
% 23.47/3.51  
% 23.47/3.51  abstr_ref_over_cycles:                  0
% 23.47/3.51  abstr_ref_under_cycles:                 0
% 23.47/3.51  gc_basic_clause_elim:                   0
% 23.47/3.51  forced_gc_time:                         0
% 23.47/3.51  parsing_time:                           0.023
% 23.47/3.51  unif_index_cands_time:                  0.
% 23.47/3.51  unif_index_add_time:                    0.
% 23.47/3.51  orderings_time:                         0.
% 23.47/3.51  out_proof_time:                         0.03
% 23.47/3.51  total_time:                             2.557
% 23.47/3.51  num_of_symbols:                         60
% 23.47/3.51  num_of_terms:                           99586
% 23.47/3.51  
% 23.47/3.51  ------ Preprocessing
% 23.47/3.51  
% 23.47/3.51  num_of_splits:                          0
% 23.47/3.51  num_of_split_atoms:                     0
% 23.47/3.51  num_of_reused_defs:                     0
% 23.47/3.51  num_eq_ax_congr_red:                    14
% 23.47/3.51  num_of_sem_filtered_clauses:            1
% 23.47/3.51  num_of_subtypes:                        3
% 23.47/3.51  monotx_restored_types:                  0
% 23.47/3.51  sat_num_of_epr_types:                   0
% 23.47/3.51  sat_num_of_non_cyclic_types:            0
% 23.47/3.51  sat_guarded_non_collapsed_types:        1
% 23.47/3.51  num_pure_diseq_elim:                    0
% 23.47/3.51  simp_replaced_by:                       0
% 23.47/3.51  res_preprocessed:                       170
% 23.47/3.51  prep_upred:                             0
% 23.47/3.51  prep_unflattend:                        32
% 23.47/3.51  smt_new_axioms:                         0
% 23.47/3.51  pred_elim_cands:                        6
% 23.47/3.51  pred_elim:                              3
% 23.47/3.51  pred_elim_cl:                           5
% 23.47/3.51  pred_elim_cycles:                       7
% 23.47/3.51  merged_defs:                            8
% 23.47/3.51  merged_defs_ncl:                        0
% 23.47/3.51  bin_hyper_res:                          8
% 23.47/3.51  prep_cycles:                            4
% 23.47/3.51  pred_elim_time:                         0.013
% 23.47/3.51  splitting_time:                         0.
% 23.47/3.51  sem_filter_time:                        0.
% 23.47/3.51  monotx_time:                            0.
% 23.47/3.51  subtype_inf_time:                       0.001
% 23.47/3.51  
% 23.47/3.51  ------ Problem properties
% 23.47/3.51  
% 23.47/3.51  clauses:                                32
% 23.47/3.51  conjectures:                            13
% 23.47/3.51  epr:                                    9
% 23.47/3.51  horn:                                   25
% 23.47/3.51  ground:                                 14
% 23.47/3.51  unary:                                  14
% 23.47/3.51  binary:                                 6
% 23.47/3.51  lits:                                   130
% 23.47/3.51  lits_eq:                                19
% 23.47/3.51  fd_pure:                                0
% 23.47/3.51  fd_pseudo:                              0
% 23.47/3.51  fd_cond:                                0
% 23.47/3.51  fd_pseudo_cond:                         1
% 23.47/3.51  ac_symbols:                             0
% 23.47/3.51  
% 23.47/3.51  ------ Propositional Solver
% 23.47/3.51  
% 23.47/3.51  prop_solver_calls:                      32
% 23.47/3.51  prop_fast_solver_calls:                 7458
% 23.47/3.51  smt_solver_calls:                       0
% 23.47/3.51  smt_fast_solver_calls:                  0
% 23.47/3.51  prop_num_of_clauses:                    19548
% 23.47/3.51  prop_preprocess_simplified:             31033
% 23.47/3.51  prop_fo_subsumed:                       644
% 23.47/3.51  prop_solver_time:                       0.
% 23.47/3.51  smt_solver_time:                        0.
% 23.47/3.51  smt_fast_solver_time:                   0.
% 23.47/3.51  prop_fast_solver_time:                  0.
% 23.47/3.51  prop_unsat_core_time:                   0.002
% 23.47/3.51  
% 23.47/3.51  ------ QBF
% 23.47/3.51  
% 23.47/3.51  qbf_q_res:                              0
% 23.47/3.51  qbf_num_tautologies:                    0
% 23.47/3.51  qbf_prep_cycles:                        0
% 23.47/3.51  
% 23.47/3.51  ------ BMC1
% 23.47/3.51  
% 23.47/3.51  bmc1_current_bound:                     -1
% 23.47/3.51  bmc1_last_solved_bound:                 -1
% 23.47/3.51  bmc1_unsat_core_size:                   -1
% 23.47/3.51  bmc1_unsat_core_parents_size:           -1
% 23.47/3.51  bmc1_merge_next_fun:                    0
% 23.47/3.51  bmc1_unsat_core_clauses_time:           0.
% 23.47/3.51  
% 23.47/3.51  ------ Instantiation
% 23.47/3.51  
% 23.47/3.51  inst_num_of_clauses:                    4569
% 23.47/3.51  inst_num_in_passive:                    277
% 23.47/3.51  inst_num_in_active:                     2351
% 23.47/3.51  inst_num_in_unprocessed:                1941
% 23.47/3.51  inst_num_of_loops:                      2580
% 23.47/3.51  inst_num_of_learning_restarts:          0
% 23.47/3.51  inst_num_moves_active_passive:          226
% 23.47/3.51  inst_lit_activity:                      0
% 23.47/3.51  inst_lit_activity_moves:                2
% 23.47/3.51  inst_num_tautologies:                   0
% 23.47/3.51  inst_num_prop_implied:                  0
% 23.47/3.51  inst_num_existing_simplified:           0
% 23.47/3.51  inst_num_eq_res_simplified:             0
% 23.47/3.51  inst_num_child_elim:                    0
% 23.47/3.51  inst_num_of_dismatching_blockings:      2396
% 23.47/3.51  inst_num_of_non_proper_insts:           4705
% 23.47/3.51  inst_num_of_duplicates:                 0
% 23.47/3.51  inst_inst_num_from_inst_to_res:         0
% 23.47/3.51  inst_dismatching_checking_time:         0.
% 23.47/3.51  
% 23.47/3.51  ------ Resolution
% 23.47/3.51  
% 23.47/3.51  res_num_of_clauses:                     0
% 23.47/3.51  res_num_in_passive:                     0
% 23.47/3.51  res_num_in_active:                      0
% 23.47/3.51  res_num_of_loops:                       174
% 23.47/3.51  res_forward_subset_subsumed:            97
% 23.47/3.51  res_backward_subset_subsumed:           0
% 23.47/3.51  res_forward_subsumed:                   0
% 23.47/3.51  res_backward_subsumed:                  0
% 23.47/3.51  res_forward_subsumption_resolution:     1
% 23.47/3.51  res_backward_subsumption_resolution:    0
% 23.47/3.51  res_clause_to_clause_subsumption:       2423
% 23.47/3.51  res_orphan_elimination:                 0
% 23.47/3.51  res_tautology_del:                      57
% 23.47/3.51  res_num_eq_res_simplified:              0
% 23.47/3.51  res_num_sel_changes:                    0
% 23.47/3.51  res_moves_from_active_to_pass:          0
% 23.47/3.51  
% 23.47/3.51  ------ Superposition
% 23.47/3.51  
% 23.47/3.51  sup_time_total:                         0.
% 23.47/3.51  sup_time_generating:                    0.
% 23.47/3.51  sup_time_sim_full:                      0.
% 23.47/3.51  sup_time_sim_immed:                     0.
% 23.47/3.51  
% 23.47/3.51  sup_num_of_clauses:                     684
% 23.47/3.51  sup_num_in_active:                      445
% 23.47/3.51  sup_num_in_passive:                     239
% 23.47/3.51  sup_num_of_loops:                       514
% 23.47/3.51  sup_fw_superposition:                   621
% 23.47/3.51  sup_bw_superposition:                   254
% 23.47/3.51  sup_immediate_simplified:               408
% 23.47/3.51  sup_given_eliminated:                   1
% 23.47/3.51  comparisons_done:                       0
% 23.47/3.51  comparisons_avoided:                    0
% 23.47/3.51  
% 23.47/3.51  ------ Simplifications
% 23.47/3.51  
% 23.47/3.51  
% 23.47/3.51  sim_fw_subset_subsumed:                 12
% 23.47/3.51  sim_bw_subset_subsumed:                 0
% 23.47/3.51  sim_fw_subsumed:                        62
% 23.47/3.51  sim_bw_subsumed:                        29
% 23.47/3.51  sim_fw_subsumption_res:                 0
% 23.47/3.51  sim_bw_subsumption_res:                 0
% 23.47/3.51  sim_tautology_del:                      0
% 23.47/3.51  sim_eq_tautology_del:                   18
% 23.47/3.51  sim_eq_res_simp:                        12
% 23.47/3.51  sim_fw_demodulated:                     233
% 23.47/3.51  sim_bw_demodulated:                     44
% 23.47/3.51  sim_light_normalised:                   253
% 23.47/3.51  sim_joinable_taut:                      0
% 23.47/3.51  sim_joinable_simp:                      0
% 23.47/3.51  sim_ac_normalised:                      0
% 23.47/3.51  sim_smt_subsumption:                    0
% 23.47/3.51  
%------------------------------------------------------------------------------
