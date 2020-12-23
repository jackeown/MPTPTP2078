%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:36 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  224 (2219 expanded)
%              Number of clauses        :  134 ( 619 expanded)
%              Number of leaves         :   23 ( 781 expanded)
%              Depth                    :   25
%              Number of atoms          : 1143 (23938 expanded)
%              Number of equality atoms :  407 (5727 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4
          | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK7,X3,X1)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6
              | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK6,X2,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4
                  | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1)))
                & v1_funct_2(X5,sK5,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
                    ( ( k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4
                      | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
                & v1_funct_2(X4,sK4,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK4,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3)))
                        & v1_funct_2(X5,X3,sK3)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3)))
                    & v1_funct_2(X4,X2,sK3)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
                          ( ( k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK2))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK2))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    & v1_funct_2(sK7,sK5,sK3)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    & v1_funct_2(sK6,sK4,sK3)
    & v1_funct_1(sK6)
    & r1_subset_1(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & ~ v1_xboole_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f36,f52,f51,f50,f49,f48,f47])).

fof(f82,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f86,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f14,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f77,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f53])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f72])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1134,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1971,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | k9_subset_1(X1_55,X2_55,X0_55) = k1_setfam_1(k2_tarski(X2_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1957,plain,
    ( k9_subset_1(X0_55,X1_55,X2_55) = k1_setfam_1(k2_tarski(X1_55,X2_55))
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_2943,plain,
    ( k9_subset_1(sK2,X0_55,sK5) = k1_setfam_1(k2_tarski(X0_55,sK5)) ),
    inference(superposition,[status(thm)],[c_1971,c_1957])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1137,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1968,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1146,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1960,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1146])).

cnf(c_3773,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_55) = k7_relat_1(sK6,X0_55)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1968,c_1960])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_43,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3873,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_55) = k7_relat_1(sK6,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3773,c_43])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1140,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1965,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_3772,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_55) = k7_relat_1(sK7,X0_55)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1960])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_46,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3868,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_55) = k7_relat_1(sK7,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3772,c_46])).

cnf(c_18,plain,
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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_21,plain,
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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,plain,
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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_19,plain,
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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_194,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_21,c_20,c_19])).

cnf(c_195,plain,
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
    inference(renaming,[status(thm)],[c_194])).

cnf(c_1128,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
    inference(subtyping,[status(esa)],[c_195])).

cnf(c_1977,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
    | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_4490,plain,
    ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3868,c_1977])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_47,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6106,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
    | k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4490,c_37,c_40,c_46,c_47,c_48])).

cnf(c_6107,plain,
    ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_6106])).

cnf(c_6113,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3873,c_6107])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_38,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6193,plain,
    ( v1_xboole_0(X0_55) = iProver_top
    | k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6113,c_38,c_43,c_44,c_45])).

cnf(c_6194,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_6193])).

cnf(c_6199,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2943,c_6194])).

cnf(c_12,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_505,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_506,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_33,c_31])).

cnf(c_1125,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_508])).

cnf(c_1980,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1154,plain,
    ( ~ r1_xboole_0(X0_55,X1_55)
    | k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1952,plain,
    ( k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0
    | r1_xboole_0(X0_55,X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_2880,plain,
    ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1980,c_1952])).

cnf(c_6200,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6199,c_2880])).

cnf(c_6201,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6200,c_2943])).

cnf(c_6202,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6201,c_2880])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6203,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6202])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_10])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_466,c_14,c_13,c_10])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | k7_relat_1(X0_55,X1_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_470])).

cnf(c_1979,plain,
    ( k7_relat_1(X0_55,X1_55) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_6789,plain,
    ( k7_relat_1(sK7,sK5) = sK7 ),
    inference(superposition,[status(thm)],[c_1965,c_1979])).

cnf(c_1147,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1959,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_3048,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1959])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1153,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1953,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1151,plain,
    ( r1_xboole_0(X0_55,X1_55)
    | r2_hidden(sK1(X0_55,X1_55),X1_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1955,plain,
    ( r1_xboole_0(X0_55,X1_55) = iProver_top
    | r2_hidden(sK1(X0_55,X1_55),X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1156,plain,
    ( ~ r2_hidden(X0_58,X0_55)
    | ~ v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1950,plain,
    ( r2_hidden(X0_58,X0_55) != iProver_top
    | v1_xboole_0(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_2950,plain,
    ( r1_xboole_0(X0_55,X1_55) = iProver_top
    | v1_xboole_0(X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_1950])).

cnf(c_4178,plain,
    ( k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0
    | v1_xboole_0(X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_2950,c_1952])).

cnf(c_4622,plain,
    ( k1_setfam_1(k2_tarski(X0_55,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1953,c_4178])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1155,plain,
    ( r1_xboole_0(X0_55,X1_55)
    | k1_setfam_1(k2_tarski(X0_55,X1_55)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1951,plain,
    ( k1_setfam_1(k2_tarski(X0_55,X1_55)) != k1_xboole_0
    | r1_xboole_0(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_4624,plain,
    ( r1_xboole_0(X0_55,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4622,c_1951])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1148,plain,
    ( ~ r1_xboole_0(X0_55,X1_55)
    | ~ v1_relat_1(X2_55)
    | k7_relat_1(k7_relat_1(X2_55,X0_55),X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1958,plain,
    ( k7_relat_1(k7_relat_1(X0_55,X1_55),X2_55) = k1_xboole_0
    | r1_xboole_0(X1_55,X2_55) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_5409,plain,
    ( k7_relat_1(k7_relat_1(X0_55,X1_55),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_4624,c_1958])).

cnf(c_6871,plain,
    ( k7_relat_1(k7_relat_1(sK7,X0_55),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3048,c_5409])).

cnf(c_6948,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6789,c_6871])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1141,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3199,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(demodulation,[status(thm)],[c_2943,c_1141])).

cnf(c_3200,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3199,c_2880])).

cnf(c_3871,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3868,c_3200])).

cnf(c_4002,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3871,c_3873])).

cnf(c_6949,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6948,c_4002])).

cnf(c_6790,plain,
    ( k7_relat_1(sK6,sK4) = sK6 ),
    inference(superposition,[status(thm)],[c_1968,c_1979])).

cnf(c_3049,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1968,c_1959])).

cnf(c_6872,plain,
    ( k7_relat_1(k7_relat_1(sK6,X0_55),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3049,c_5409])).

cnf(c_6966,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6790,c_6872])).

cnf(c_17,plain,
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
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_201,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_21,c_20,c_19])).

cnf(c_202,plain,
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
    inference(renaming,[status(thm)],[c_201])).

cnf(c_1127,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_1978,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
    | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_6379,plain,
    ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3868,c_1978])).

cnf(c_7230,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
    | k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6379,c_37,c_40,c_46,c_47,c_48])).

cnf(c_7231,plain,
    ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
    | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_7230])).

cnf(c_7237,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3873,c_7231])).

cnf(c_7272,plain,
    ( v1_xboole_0(X0_55) = iProver_top
    | k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7237,c_38,c_43,c_44,c_45])).

cnf(c_7273,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_7272])).

cnf(c_7278,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2943,c_7273])).

cnf(c_7279,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7278,c_2880,c_6948])).

cnf(c_7280,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7279,c_2943])).

cnf(c_7281,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7280,c_2880,c_6966])).

cnf(c_7282,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7281])).

cnf(c_11701,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6202,c_35,c_36,c_32,c_39,c_30,c_41,c_6203,c_6949,c_6966,c_7282])).

cnf(c_11703,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11701,c_6948,c_6966])).

cnf(c_11704,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11703])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.69/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/1.51  
% 7.69/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.69/1.51  
% 7.69/1.51  ------  iProver source info
% 7.69/1.51  
% 7.69/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.69/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.69/1.51  git: non_committed_changes: false
% 7.69/1.51  git: last_make_outside_of_git: false
% 7.69/1.51  
% 7.69/1.51  ------ 
% 7.69/1.51  
% 7.69/1.51  ------ Input Options
% 7.69/1.51  
% 7.69/1.51  --out_options                           all
% 7.69/1.51  --tptp_safe_out                         true
% 7.69/1.51  --problem_path                          ""
% 7.69/1.51  --include_path                          ""
% 7.69/1.51  --clausifier                            res/vclausify_rel
% 7.69/1.51  --clausifier_options                    ""
% 7.69/1.51  --stdin                                 false
% 7.69/1.51  --stats_out                             all
% 7.69/1.51  
% 7.69/1.51  ------ General Options
% 7.69/1.51  
% 7.69/1.51  --fof                                   false
% 7.69/1.51  --time_out_real                         305.
% 7.69/1.51  --time_out_virtual                      -1.
% 7.69/1.51  --symbol_type_check                     false
% 7.69/1.51  --clausify_out                          false
% 7.69/1.51  --sig_cnt_out                           false
% 7.69/1.51  --trig_cnt_out                          false
% 7.69/1.51  --trig_cnt_out_tolerance                1.
% 7.69/1.51  --trig_cnt_out_sk_spl                   false
% 7.69/1.51  --abstr_cl_out                          false
% 7.69/1.51  
% 7.69/1.51  ------ Global Options
% 7.69/1.51  
% 7.69/1.51  --schedule                              default
% 7.69/1.51  --add_important_lit                     false
% 7.69/1.51  --prop_solver_per_cl                    1000
% 7.69/1.51  --min_unsat_core                        false
% 7.69/1.51  --soft_assumptions                      false
% 7.69/1.51  --soft_lemma_size                       3
% 7.69/1.51  --prop_impl_unit_size                   0
% 7.69/1.51  --prop_impl_unit                        []
% 7.69/1.51  --share_sel_clauses                     true
% 7.69/1.51  --reset_solvers                         false
% 7.69/1.51  --bc_imp_inh                            [conj_cone]
% 7.69/1.51  --conj_cone_tolerance                   3.
% 7.69/1.51  --extra_neg_conj                        none
% 7.69/1.51  --large_theory_mode                     true
% 7.69/1.51  --prolific_symb_bound                   200
% 7.69/1.51  --lt_threshold                          2000
% 7.69/1.51  --clause_weak_htbl                      true
% 7.69/1.51  --gc_record_bc_elim                     false
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing Options
% 7.69/1.51  
% 7.69/1.51  --preprocessing_flag                    true
% 7.69/1.51  --time_out_prep_mult                    0.1
% 7.69/1.51  --splitting_mode                        input
% 7.69/1.51  --splitting_grd                         true
% 7.69/1.51  --splitting_cvd                         false
% 7.69/1.51  --splitting_cvd_svl                     false
% 7.69/1.51  --splitting_nvd                         32
% 7.69/1.51  --sub_typing                            true
% 7.69/1.51  --prep_gs_sim                           true
% 7.69/1.51  --prep_unflatten                        true
% 7.69/1.51  --prep_res_sim                          true
% 7.69/1.51  --prep_upred                            true
% 7.69/1.51  --prep_sem_filter                       exhaustive
% 7.69/1.51  --prep_sem_filter_out                   false
% 7.69/1.51  --pred_elim                             true
% 7.69/1.51  --res_sim_input                         true
% 7.69/1.51  --eq_ax_congr_red                       true
% 7.69/1.51  --pure_diseq_elim                       true
% 7.69/1.51  --brand_transform                       false
% 7.69/1.51  --non_eq_to_eq                          false
% 7.69/1.51  --prep_def_merge                        true
% 7.69/1.51  --prep_def_merge_prop_impl              false
% 7.69/1.51  --prep_def_merge_mbd                    true
% 7.69/1.51  --prep_def_merge_tr_red                 false
% 7.69/1.51  --prep_def_merge_tr_cl                  false
% 7.69/1.51  --smt_preprocessing                     true
% 7.69/1.51  --smt_ac_axioms                         fast
% 7.69/1.51  --preprocessed_out                      false
% 7.69/1.51  --preprocessed_stats                    false
% 7.69/1.51  
% 7.69/1.51  ------ Abstraction refinement Options
% 7.69/1.51  
% 7.69/1.51  --abstr_ref                             []
% 7.69/1.51  --abstr_ref_prep                        false
% 7.69/1.51  --abstr_ref_until_sat                   false
% 7.69/1.51  --abstr_ref_sig_restrict                funpre
% 7.69/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.51  --abstr_ref_under                       []
% 7.69/1.51  
% 7.69/1.51  ------ SAT Options
% 7.69/1.51  
% 7.69/1.51  --sat_mode                              false
% 7.69/1.51  --sat_fm_restart_options                ""
% 7.69/1.51  --sat_gr_def                            false
% 7.69/1.51  --sat_epr_types                         true
% 7.69/1.51  --sat_non_cyclic_types                  false
% 7.69/1.51  --sat_finite_models                     false
% 7.69/1.51  --sat_fm_lemmas                         false
% 7.69/1.51  --sat_fm_prep                           false
% 7.69/1.51  --sat_fm_uc_incr                        true
% 7.69/1.51  --sat_out_model                         small
% 7.69/1.51  --sat_out_clauses                       false
% 7.69/1.51  
% 7.69/1.51  ------ QBF Options
% 7.69/1.51  
% 7.69/1.51  --qbf_mode                              false
% 7.69/1.51  --qbf_elim_univ                         false
% 7.69/1.51  --qbf_dom_inst                          none
% 7.69/1.51  --qbf_dom_pre_inst                      false
% 7.69/1.51  --qbf_sk_in                             false
% 7.69/1.51  --qbf_pred_elim                         true
% 7.69/1.51  --qbf_split                             512
% 7.69/1.51  
% 7.69/1.51  ------ BMC1 Options
% 7.69/1.51  
% 7.69/1.51  --bmc1_incremental                      false
% 7.69/1.51  --bmc1_axioms                           reachable_all
% 7.69/1.51  --bmc1_min_bound                        0
% 7.69/1.51  --bmc1_max_bound                        -1
% 7.69/1.51  --bmc1_max_bound_default                -1
% 7.69/1.51  --bmc1_symbol_reachability              true
% 7.69/1.51  --bmc1_property_lemmas                  false
% 7.69/1.51  --bmc1_k_induction                      false
% 7.69/1.51  --bmc1_non_equiv_states                 false
% 7.69/1.51  --bmc1_deadlock                         false
% 7.69/1.51  --bmc1_ucm                              false
% 7.69/1.51  --bmc1_add_unsat_core                   none
% 7.69/1.51  --bmc1_unsat_core_children              false
% 7.69/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.51  --bmc1_out_stat                         full
% 7.69/1.51  --bmc1_ground_init                      false
% 7.69/1.51  --bmc1_pre_inst_next_state              false
% 7.69/1.51  --bmc1_pre_inst_state                   false
% 7.69/1.51  --bmc1_pre_inst_reach_state             false
% 7.69/1.51  --bmc1_out_unsat_core                   false
% 7.69/1.51  --bmc1_aig_witness_out                  false
% 7.69/1.51  --bmc1_verbose                          false
% 7.69/1.51  --bmc1_dump_clauses_tptp                false
% 7.69/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.51  --bmc1_dump_file                        -
% 7.69/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.51  --bmc1_ucm_extend_mode                  1
% 7.69/1.51  --bmc1_ucm_init_mode                    2
% 7.69/1.51  --bmc1_ucm_cone_mode                    none
% 7.69/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.51  --bmc1_ucm_relax_model                  4
% 7.69/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.51  --bmc1_ucm_layered_model                none
% 7.69/1.51  --bmc1_ucm_max_lemma_size               10
% 7.69/1.51  
% 7.69/1.51  ------ AIG Options
% 7.69/1.51  
% 7.69/1.51  --aig_mode                              false
% 7.69/1.51  
% 7.69/1.51  ------ Instantiation Options
% 7.69/1.51  
% 7.69/1.51  --instantiation_flag                    true
% 7.69/1.51  --inst_sos_flag                         true
% 7.69/1.51  --inst_sos_phase                        true
% 7.69/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.51  --inst_lit_sel_side                     num_symb
% 7.69/1.51  --inst_solver_per_active                1400
% 7.69/1.51  --inst_solver_calls_frac                1.
% 7.69/1.51  --inst_passive_queue_type               priority_queues
% 7.69/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.51  --inst_passive_queues_freq              [25;2]
% 7.69/1.51  --inst_dismatching                      true
% 7.69/1.51  --inst_eager_unprocessed_to_passive     true
% 7.69/1.51  --inst_prop_sim_given                   true
% 7.69/1.51  --inst_prop_sim_new                     false
% 7.69/1.51  --inst_subs_new                         false
% 7.69/1.51  --inst_eq_res_simp                      false
% 7.69/1.51  --inst_subs_given                       false
% 7.69/1.51  --inst_orphan_elimination               true
% 7.69/1.51  --inst_learning_loop_flag               true
% 7.69/1.51  --inst_learning_start                   3000
% 7.69/1.51  --inst_learning_factor                  2
% 7.69/1.51  --inst_start_prop_sim_after_learn       3
% 7.69/1.51  --inst_sel_renew                        solver
% 7.69/1.51  --inst_lit_activity_flag                true
% 7.69/1.51  --inst_restr_to_given                   false
% 7.69/1.51  --inst_activity_threshold               500
% 7.69/1.51  --inst_out_proof                        true
% 7.69/1.51  
% 7.69/1.51  ------ Resolution Options
% 7.69/1.51  
% 7.69/1.51  --resolution_flag                       true
% 7.69/1.51  --res_lit_sel                           adaptive
% 7.69/1.51  --res_lit_sel_side                      none
% 7.69/1.51  --res_ordering                          kbo
% 7.69/1.51  --res_to_prop_solver                    active
% 7.69/1.51  --res_prop_simpl_new                    false
% 7.69/1.51  --res_prop_simpl_given                  true
% 7.69/1.51  --res_passive_queue_type                priority_queues
% 7.69/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.51  --res_passive_queues_freq               [15;5]
% 7.69/1.51  --res_forward_subs                      full
% 7.69/1.51  --res_backward_subs                     full
% 7.69/1.51  --res_forward_subs_resolution           true
% 7.69/1.51  --res_backward_subs_resolution          true
% 7.69/1.51  --res_orphan_elimination                true
% 7.69/1.51  --res_time_limit                        2.
% 7.69/1.51  --res_out_proof                         true
% 7.69/1.51  
% 7.69/1.51  ------ Superposition Options
% 7.69/1.51  
% 7.69/1.51  --superposition_flag                    true
% 7.69/1.51  --sup_passive_queue_type                priority_queues
% 7.69/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.69/1.51  --demod_completeness_check              fast
% 7.69/1.51  --demod_use_ground                      true
% 7.69/1.51  --sup_to_prop_solver                    passive
% 7.69/1.51  --sup_prop_simpl_new                    true
% 7.69/1.51  --sup_prop_simpl_given                  true
% 7.69/1.51  --sup_fun_splitting                     true
% 7.69/1.51  --sup_smt_interval                      50000
% 7.69/1.51  
% 7.69/1.51  ------ Superposition Simplification Setup
% 7.69/1.51  
% 7.69/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.69/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.69/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.69/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.69/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.69/1.51  --sup_immed_triv                        [TrivRules]
% 7.69/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.51  --sup_immed_bw_main                     []
% 7.69/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.69/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.51  --sup_input_bw                          []
% 7.69/1.51  
% 7.69/1.51  ------ Combination Options
% 7.69/1.51  
% 7.69/1.51  --comb_res_mult                         3
% 7.69/1.51  --comb_sup_mult                         2
% 7.69/1.51  --comb_inst_mult                        10
% 7.69/1.51  
% 7.69/1.51  ------ Debug Options
% 7.69/1.51  
% 7.69/1.51  --dbg_backtrace                         false
% 7.69/1.51  --dbg_dump_prop_clauses                 false
% 7.69/1.51  --dbg_dump_prop_clauses_file            -
% 7.69/1.51  --dbg_out_stat                          false
% 7.69/1.51  ------ Parsing...
% 7.69/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.69/1.51  ------ Proving...
% 7.69/1.51  ------ Problem Properties 
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  clauses                                 33
% 7.69/1.51  conjectures                             13
% 7.69/1.51  EPR                                     12
% 7.69/1.51  Horn                                    24
% 7.69/1.51  unary                                   14
% 7.69/1.51  binary                                  9
% 7.69/1.51  lits                                    128
% 7.69/1.51  lits eq                                 15
% 7.69/1.51  fd_pure                                 0
% 7.69/1.51  fd_pseudo                               0
% 7.69/1.51  fd_cond                                 0
% 7.69/1.51  fd_pseudo_cond                          0
% 7.69/1.51  AC symbols                              0
% 7.69/1.51  
% 7.69/1.51  ------ Schedule dynamic 5 is on 
% 7.69/1.51  
% 7.69/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  ------ 
% 7.69/1.51  Current options:
% 7.69/1.51  ------ 
% 7.69/1.51  
% 7.69/1.51  ------ Input Options
% 7.69/1.51  
% 7.69/1.51  --out_options                           all
% 7.69/1.51  --tptp_safe_out                         true
% 7.69/1.51  --problem_path                          ""
% 7.69/1.51  --include_path                          ""
% 7.69/1.51  --clausifier                            res/vclausify_rel
% 7.69/1.51  --clausifier_options                    ""
% 7.69/1.51  --stdin                                 false
% 7.69/1.51  --stats_out                             all
% 7.69/1.51  
% 7.69/1.51  ------ General Options
% 7.69/1.51  
% 7.69/1.51  --fof                                   false
% 7.69/1.51  --time_out_real                         305.
% 7.69/1.51  --time_out_virtual                      -1.
% 7.69/1.51  --symbol_type_check                     false
% 7.69/1.51  --clausify_out                          false
% 7.69/1.51  --sig_cnt_out                           false
% 7.69/1.51  --trig_cnt_out                          false
% 7.69/1.51  --trig_cnt_out_tolerance                1.
% 7.69/1.51  --trig_cnt_out_sk_spl                   false
% 7.69/1.51  --abstr_cl_out                          false
% 7.69/1.51  
% 7.69/1.51  ------ Global Options
% 7.69/1.51  
% 7.69/1.51  --schedule                              default
% 7.69/1.51  --add_important_lit                     false
% 7.69/1.51  --prop_solver_per_cl                    1000
% 7.69/1.51  --min_unsat_core                        false
% 7.69/1.51  --soft_assumptions                      false
% 7.69/1.51  --soft_lemma_size                       3
% 7.69/1.51  --prop_impl_unit_size                   0
% 7.69/1.51  --prop_impl_unit                        []
% 7.69/1.51  --share_sel_clauses                     true
% 7.69/1.51  --reset_solvers                         false
% 7.69/1.51  --bc_imp_inh                            [conj_cone]
% 7.69/1.51  --conj_cone_tolerance                   3.
% 7.69/1.51  --extra_neg_conj                        none
% 7.69/1.51  --large_theory_mode                     true
% 7.69/1.51  --prolific_symb_bound                   200
% 7.69/1.51  --lt_threshold                          2000
% 7.69/1.51  --clause_weak_htbl                      true
% 7.69/1.51  --gc_record_bc_elim                     false
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing Options
% 7.69/1.51  
% 7.69/1.51  --preprocessing_flag                    true
% 7.69/1.51  --time_out_prep_mult                    0.1
% 7.69/1.51  --splitting_mode                        input
% 7.69/1.51  --splitting_grd                         true
% 7.69/1.51  --splitting_cvd                         false
% 7.69/1.51  --splitting_cvd_svl                     false
% 7.69/1.51  --splitting_nvd                         32
% 7.69/1.51  --sub_typing                            true
% 7.69/1.51  --prep_gs_sim                           true
% 7.69/1.51  --prep_unflatten                        true
% 7.69/1.51  --prep_res_sim                          true
% 7.69/1.51  --prep_upred                            true
% 7.69/1.51  --prep_sem_filter                       exhaustive
% 7.69/1.51  --prep_sem_filter_out                   false
% 7.69/1.51  --pred_elim                             true
% 7.69/1.51  --res_sim_input                         true
% 7.69/1.51  --eq_ax_congr_red                       true
% 7.69/1.51  --pure_diseq_elim                       true
% 7.69/1.51  --brand_transform                       false
% 7.69/1.51  --non_eq_to_eq                          false
% 7.69/1.51  --prep_def_merge                        true
% 7.69/1.51  --prep_def_merge_prop_impl              false
% 7.69/1.51  --prep_def_merge_mbd                    true
% 7.69/1.51  --prep_def_merge_tr_red                 false
% 7.69/1.51  --prep_def_merge_tr_cl                  false
% 7.69/1.51  --smt_preprocessing                     true
% 7.69/1.51  --smt_ac_axioms                         fast
% 7.69/1.51  --preprocessed_out                      false
% 7.69/1.51  --preprocessed_stats                    false
% 7.69/1.51  
% 7.69/1.51  ------ Abstraction refinement Options
% 7.69/1.51  
% 7.69/1.51  --abstr_ref                             []
% 7.69/1.51  --abstr_ref_prep                        false
% 7.69/1.51  --abstr_ref_until_sat                   false
% 7.69/1.51  --abstr_ref_sig_restrict                funpre
% 7.69/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.51  --abstr_ref_under                       []
% 7.69/1.51  
% 7.69/1.51  ------ SAT Options
% 7.69/1.51  
% 7.69/1.51  --sat_mode                              false
% 7.69/1.51  --sat_fm_restart_options                ""
% 7.69/1.51  --sat_gr_def                            false
% 7.69/1.51  --sat_epr_types                         true
% 7.69/1.51  --sat_non_cyclic_types                  false
% 7.69/1.51  --sat_finite_models                     false
% 7.69/1.51  --sat_fm_lemmas                         false
% 7.69/1.51  --sat_fm_prep                           false
% 7.69/1.51  --sat_fm_uc_incr                        true
% 7.69/1.51  --sat_out_model                         small
% 7.69/1.51  --sat_out_clauses                       false
% 7.69/1.51  
% 7.69/1.51  ------ QBF Options
% 7.69/1.51  
% 7.69/1.51  --qbf_mode                              false
% 7.69/1.51  --qbf_elim_univ                         false
% 7.69/1.51  --qbf_dom_inst                          none
% 7.69/1.51  --qbf_dom_pre_inst                      false
% 7.69/1.51  --qbf_sk_in                             false
% 7.69/1.51  --qbf_pred_elim                         true
% 7.69/1.51  --qbf_split                             512
% 7.69/1.51  
% 7.69/1.51  ------ BMC1 Options
% 7.69/1.51  
% 7.69/1.51  --bmc1_incremental                      false
% 7.69/1.51  --bmc1_axioms                           reachable_all
% 7.69/1.51  --bmc1_min_bound                        0
% 7.69/1.51  --bmc1_max_bound                        -1
% 7.69/1.51  --bmc1_max_bound_default                -1
% 7.69/1.51  --bmc1_symbol_reachability              true
% 7.69/1.51  --bmc1_property_lemmas                  false
% 7.69/1.51  --bmc1_k_induction                      false
% 7.69/1.51  --bmc1_non_equiv_states                 false
% 7.69/1.51  --bmc1_deadlock                         false
% 7.69/1.51  --bmc1_ucm                              false
% 7.69/1.51  --bmc1_add_unsat_core                   none
% 7.69/1.51  --bmc1_unsat_core_children              false
% 7.69/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.51  --bmc1_out_stat                         full
% 7.69/1.51  --bmc1_ground_init                      false
% 7.69/1.51  --bmc1_pre_inst_next_state              false
% 7.69/1.51  --bmc1_pre_inst_state                   false
% 7.69/1.51  --bmc1_pre_inst_reach_state             false
% 7.69/1.51  --bmc1_out_unsat_core                   false
% 7.69/1.51  --bmc1_aig_witness_out                  false
% 7.69/1.51  --bmc1_verbose                          false
% 7.69/1.51  --bmc1_dump_clauses_tptp                false
% 7.69/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.51  --bmc1_dump_file                        -
% 7.69/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.51  --bmc1_ucm_extend_mode                  1
% 7.69/1.51  --bmc1_ucm_init_mode                    2
% 7.69/1.51  --bmc1_ucm_cone_mode                    none
% 7.69/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.51  --bmc1_ucm_relax_model                  4
% 7.69/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.51  --bmc1_ucm_layered_model                none
% 7.69/1.51  --bmc1_ucm_max_lemma_size               10
% 7.69/1.51  
% 7.69/1.51  ------ AIG Options
% 7.69/1.51  
% 7.69/1.51  --aig_mode                              false
% 7.69/1.51  
% 7.69/1.51  ------ Instantiation Options
% 7.69/1.51  
% 7.69/1.51  --instantiation_flag                    true
% 7.69/1.51  --inst_sos_flag                         true
% 7.69/1.51  --inst_sos_phase                        true
% 7.69/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.51  --inst_lit_sel_side                     none
% 7.69/1.51  --inst_solver_per_active                1400
% 7.69/1.51  --inst_solver_calls_frac                1.
% 7.69/1.51  --inst_passive_queue_type               priority_queues
% 7.69/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.51  --inst_passive_queues_freq              [25;2]
% 7.69/1.51  --inst_dismatching                      true
% 7.69/1.51  --inst_eager_unprocessed_to_passive     true
% 7.69/1.51  --inst_prop_sim_given                   true
% 7.69/1.51  --inst_prop_sim_new                     false
% 7.69/1.51  --inst_subs_new                         false
% 7.69/1.51  --inst_eq_res_simp                      false
% 7.69/1.51  --inst_subs_given                       false
% 7.69/1.51  --inst_orphan_elimination               true
% 7.69/1.51  --inst_learning_loop_flag               true
% 7.69/1.51  --inst_learning_start                   3000
% 7.69/1.51  --inst_learning_factor                  2
% 7.69/1.51  --inst_start_prop_sim_after_learn       3
% 7.69/1.51  --inst_sel_renew                        solver
% 7.69/1.51  --inst_lit_activity_flag                true
% 7.69/1.51  --inst_restr_to_given                   false
% 7.69/1.51  --inst_activity_threshold               500
% 7.69/1.51  --inst_out_proof                        true
% 7.69/1.51  
% 7.69/1.51  ------ Resolution Options
% 7.69/1.51  
% 7.69/1.51  --resolution_flag                       false
% 7.69/1.51  --res_lit_sel                           adaptive
% 7.69/1.51  --res_lit_sel_side                      none
% 7.69/1.51  --res_ordering                          kbo
% 7.69/1.51  --res_to_prop_solver                    active
% 7.69/1.51  --res_prop_simpl_new                    false
% 7.69/1.51  --res_prop_simpl_given                  true
% 7.69/1.51  --res_passive_queue_type                priority_queues
% 7.69/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.51  --res_passive_queues_freq               [15;5]
% 7.69/1.51  --res_forward_subs                      full
% 7.69/1.51  --res_backward_subs                     full
% 7.69/1.51  --res_forward_subs_resolution           true
% 7.69/1.51  --res_backward_subs_resolution          true
% 7.69/1.51  --res_orphan_elimination                true
% 7.69/1.51  --res_time_limit                        2.
% 7.69/1.51  --res_out_proof                         true
% 7.69/1.51  
% 7.69/1.51  ------ Superposition Options
% 7.69/1.51  
% 7.69/1.51  --superposition_flag                    true
% 7.69/1.51  --sup_passive_queue_type                priority_queues
% 7.69/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.69/1.51  --demod_completeness_check              fast
% 7.69/1.51  --demod_use_ground                      true
% 7.69/1.51  --sup_to_prop_solver                    passive
% 7.69/1.51  --sup_prop_simpl_new                    true
% 7.69/1.51  --sup_prop_simpl_given                  true
% 7.69/1.51  --sup_fun_splitting                     true
% 7.69/1.51  --sup_smt_interval                      50000
% 7.69/1.51  
% 7.69/1.51  ------ Superposition Simplification Setup
% 7.69/1.51  
% 7.69/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.69/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.69/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.69/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.69/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.69/1.51  --sup_immed_triv                        [TrivRules]
% 7.69/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.51  --sup_immed_bw_main                     []
% 7.69/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.69/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.51  --sup_input_bw                          []
% 7.69/1.51  
% 7.69/1.51  ------ Combination Options
% 7.69/1.51  
% 7.69/1.51  --comb_res_mult                         3
% 7.69/1.51  --comb_sup_mult                         2
% 7.69/1.51  --comb_inst_mult                        10
% 7.69/1.51  
% 7.69/1.51  ------ Debug Options
% 7.69/1.51  
% 7.69/1.51  --dbg_backtrace                         false
% 7.69/1.51  --dbg_dump_prop_clauses                 false
% 7.69/1.51  --dbg_dump_prop_clauses_file            -
% 7.69/1.51  --dbg_out_stat                          false
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  ------ Proving...
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  % SZS status Theorem for theBenchmark.p
% 7.69/1.51  
% 7.69/1.51   Resolution empty clause
% 7.69/1.51  
% 7.69/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.69/1.51  
% 7.69/1.51  fof(f15,conjecture,(
% 7.69/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f16,negated_conjecture,(
% 7.69/1.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.69/1.51    inference(negated_conjecture,[],[f15])).
% 7.69/1.51  
% 7.69/1.51  fof(f35,plain,(
% 7.69/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.69/1.51    inference(ennf_transformation,[],[f16])).
% 7.69/1.51  
% 7.69/1.51  fof(f36,plain,(
% 7.69/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.69/1.51    inference(flattening,[],[f35])).
% 7.69/1.51  
% 7.69/1.51  fof(f52,plain,(
% 7.69/1.51    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f51,plain,(
% 7.69/1.51    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f50,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f49,plain,(
% 7.69/1.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f48,plain,(
% 7.69/1.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f47,plain,(
% 7.69/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f53,plain,(
% 7.69/1.51    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.69/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f36,f52,f51,f50,f49,f48,f47])).
% 7.69/1.51  
% 7.69/1.51  fof(f82,plain,(
% 7.69/1.51    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f5,axiom,(
% 7.69/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f20,plain,(
% 7.69/1.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.69/1.51    inference(ennf_transformation,[],[f5])).
% 7.69/1.51  
% 7.69/1.51  fof(f62,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.69/1.51    inference(cnf_transformation,[],[f20])).
% 7.69/1.51  
% 7.69/1.51  fof(f6,axiom,(
% 7.69/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f63,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.69/1.51    inference(cnf_transformation,[],[f6])).
% 7.69/1.51  
% 7.69/1.51  fof(f93,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.69/1.51    inference(definition_unfolding,[],[f62,f63])).
% 7.69/1.51  
% 7.69/1.51  fof(f86,plain,(
% 7.69/1.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f12,axiom,(
% 7.69/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f29,plain,(
% 7.69/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.69/1.51    inference(ennf_transformation,[],[f12])).
% 7.69/1.51  
% 7.69/1.51  fof(f30,plain,(
% 7.69/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.69/1.51    inference(flattening,[],[f29])).
% 7.69/1.51  
% 7.69/1.51  fof(f70,plain,(
% 7.69/1.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f30])).
% 7.69/1.51  
% 7.69/1.51  fof(f84,plain,(
% 7.69/1.51    v1_funct_1(sK6)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f89,plain,(
% 7.69/1.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f87,plain,(
% 7.69/1.51    v1_funct_1(sK7)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f13,axiom,(
% 7.69/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f31,plain,(
% 7.69/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.69/1.51    inference(ennf_transformation,[],[f13])).
% 7.69/1.51  
% 7.69/1.51  fof(f32,plain,(
% 7.69/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.69/1.51    inference(flattening,[],[f31])).
% 7.69/1.51  
% 7.69/1.51  fof(f45,plain,(
% 7.69/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.69/1.51    inference(nnf_transformation,[],[f32])).
% 7.69/1.51  
% 7.69/1.51  fof(f46,plain,(
% 7.69/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.69/1.51    inference(flattening,[],[f45])).
% 7.69/1.51  
% 7.69/1.51  fof(f71,plain,(
% 7.69/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f46])).
% 7.69/1.51  
% 7.69/1.51  fof(f97,plain,(
% 7.69/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.69/1.51    inference(equality_resolution,[],[f71])).
% 7.69/1.51  
% 7.69/1.51  fof(f14,axiom,(
% 7.69/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f33,plain,(
% 7.69/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.69/1.51    inference(ennf_transformation,[],[f14])).
% 7.69/1.51  
% 7.69/1.51  fof(f34,plain,(
% 7.69/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.69/1.51    inference(flattening,[],[f33])).
% 7.69/1.51  
% 7.69/1.51  fof(f74,plain,(
% 7.69/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f34])).
% 7.69/1.51  
% 7.69/1.51  fof(f75,plain,(
% 7.69/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f34])).
% 7.69/1.51  
% 7.69/1.51  fof(f76,plain,(
% 7.69/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f34])).
% 7.69/1.51  
% 7.69/1.51  fof(f78,plain,(
% 7.69/1.51    ~v1_xboole_0(sK3)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f81,plain,(
% 7.69/1.51    ~v1_xboole_0(sK5)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f88,plain,(
% 7.69/1.51    v1_funct_2(sK7,sK5,sK3)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f79,plain,(
% 7.69/1.51    ~v1_xboole_0(sK4)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f85,plain,(
% 7.69/1.51    v1_funct_2(sK6,sK4,sK3)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f9,axiom,(
% 7.69/1.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f25,plain,(
% 7.69/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.69/1.51    inference(ennf_transformation,[],[f9])).
% 7.69/1.51  
% 7.69/1.51  fof(f26,plain,(
% 7.69/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.69/1.51    inference(flattening,[],[f25])).
% 7.69/1.51  
% 7.69/1.51  fof(f44,plain,(
% 7.69/1.51    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.69/1.51    inference(nnf_transformation,[],[f26])).
% 7.69/1.51  
% 7.69/1.51  fof(f66,plain,(
% 7.69/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f44])).
% 7.69/1.51  
% 7.69/1.51  fof(f83,plain,(
% 7.69/1.51    r1_subset_1(sK4,sK5)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f2,axiom,(
% 7.69/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f41,plain,(
% 7.69/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.69/1.51    inference(nnf_transformation,[],[f2])).
% 7.69/1.51  
% 7.69/1.51  fof(f56,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f41])).
% 7.69/1.51  
% 7.69/1.51  fof(f92,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.69/1.51    inference(definition_unfolding,[],[f56,f63])).
% 7.69/1.51  
% 7.69/1.51  fof(f77,plain,(
% 7.69/1.51    ~v1_xboole_0(sK2)),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f80,plain,(
% 7.69/1.51    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f11,axiom,(
% 7.69/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f18,plain,(
% 7.69/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.69/1.51    inference(pure_predicate_removal,[],[f11])).
% 7.69/1.51  
% 7.69/1.51  fof(f28,plain,(
% 7.69/1.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.51    inference(ennf_transformation,[],[f18])).
% 7.69/1.51  
% 7.69/1.51  fof(f69,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.51    inference(cnf_transformation,[],[f28])).
% 7.69/1.51  
% 7.69/1.51  fof(f8,axiom,(
% 7.69/1.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f23,plain,(
% 7.69/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.69/1.51    inference(ennf_transformation,[],[f8])).
% 7.69/1.51  
% 7.69/1.51  fof(f24,plain,(
% 7.69/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.69/1.51    inference(flattening,[],[f23])).
% 7.69/1.51  
% 7.69/1.51  fof(f65,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f24])).
% 7.69/1.51  
% 7.69/1.51  fof(f10,axiom,(
% 7.69/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f27,plain,(
% 7.69/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.51    inference(ennf_transformation,[],[f10])).
% 7.69/1.51  
% 7.69/1.51  fof(f68,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.51    inference(cnf_transformation,[],[f27])).
% 7.69/1.51  
% 7.69/1.51  fof(f3,axiom,(
% 7.69/1.51    v1_xboole_0(k1_xboole_0)),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f58,plain,(
% 7.69/1.51    v1_xboole_0(k1_xboole_0)),
% 7.69/1.51    inference(cnf_transformation,[],[f3])).
% 7.69/1.51  
% 7.69/1.51  fof(f4,axiom,(
% 7.69/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f17,plain,(
% 7.69/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.69/1.51    inference(rectify,[],[f4])).
% 7.69/1.51  
% 7.69/1.51  fof(f19,plain,(
% 7.69/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.69/1.51    inference(ennf_transformation,[],[f17])).
% 7.69/1.51  
% 7.69/1.51  fof(f42,plain,(
% 7.69/1.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f43,plain,(
% 7.69/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.69/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f42])).
% 7.69/1.51  
% 7.69/1.51  fof(f60,plain,(
% 7.69/1.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f43])).
% 7.69/1.51  
% 7.69/1.51  fof(f1,axiom,(
% 7.69/1.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f37,plain,(
% 7.69/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.69/1.51    inference(nnf_transformation,[],[f1])).
% 7.69/1.51  
% 7.69/1.51  fof(f38,plain,(
% 7.69/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.69/1.51    inference(rectify,[],[f37])).
% 7.69/1.51  
% 7.69/1.51  fof(f39,plain,(
% 7.69/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f40,plain,(
% 7.69/1.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.69/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 7.69/1.51  
% 7.69/1.51  fof(f54,plain,(
% 7.69/1.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f40])).
% 7.69/1.51  
% 7.69/1.51  fof(f57,plain,(
% 7.69/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.69/1.51    inference(cnf_transformation,[],[f41])).
% 7.69/1.51  
% 7.69/1.51  fof(f91,plain,(
% 7.69/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.69/1.51    inference(definition_unfolding,[],[f57,f63])).
% 7.69/1.51  
% 7.69/1.51  fof(f7,axiom,(
% 7.69/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f21,plain,(
% 7.69/1.51    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.69/1.51    inference(ennf_transformation,[],[f7])).
% 7.69/1.51  
% 7.69/1.51  fof(f22,plain,(
% 7.69/1.51    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.69/1.51    inference(flattening,[],[f21])).
% 7.69/1.51  
% 7.69/1.51  fof(f64,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f22])).
% 7.69/1.51  
% 7.69/1.51  fof(f90,plain,(
% 7.69/1.51    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 7.69/1.51    inference(cnf_transformation,[],[f53])).
% 7.69/1.51  
% 7.69/1.51  fof(f72,plain,(
% 7.69/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f46])).
% 7.69/1.51  
% 7.69/1.51  fof(f96,plain,(
% 7.69/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.69/1.51    inference(equality_resolution,[],[f72])).
% 7.69/1.51  
% 7.69/1.51  cnf(c_30,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1134,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_30]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1971,plain,
% 7.69/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_8,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.69/1.51      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1149,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 7.69/1.51      | k9_subset_1(X1_55,X2_55,X0_55) = k1_setfam_1(k2_tarski(X2_55,X0_55)) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_8]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1957,plain,
% 7.69/1.51      ( k9_subset_1(X0_55,X1_55,X2_55) = k1_setfam_1(k2_tarski(X1_55,X2_55))
% 7.69/1.51      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2943,plain,
% 7.69/1.51      ( k9_subset_1(sK2,X0_55,sK5) = k1_setfam_1(k2_tarski(X0_55,sK5)) ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1971,c_1957]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_26,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.69/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1137,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_26]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1968,plain,
% 7.69/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_15,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.69/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1146,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.69/1.51      | ~ v1_funct_1(X0_55)
% 7.69/1.51      | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_15]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1960,plain,
% 7.69/1.51      ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
% 7.69/1.51      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.69/1.51      | v1_funct_1(X2_55) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1146]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3773,plain,
% 7.69/1.51      ( k2_partfun1(sK4,sK3,sK6,X0_55) = k7_relat_1(sK6,X0_55)
% 7.69/1.51      | v1_funct_1(sK6) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1968,c_1960]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_28,negated_conjecture,
% 7.69/1.51      ( v1_funct_1(sK6) ),
% 7.69/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_43,plain,
% 7.69/1.51      ( v1_funct_1(sK6) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3873,plain,
% 7.69/1.51      ( k2_partfun1(sK4,sK3,sK6,X0_55) = k7_relat_1(sK6,X0_55) ),
% 7.69/1.51      inference(global_propositional_subsumption,[status(thm)],[c_3773,c_43]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_23,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.69/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1140,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_23]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1965,plain,
% 7.69/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1140]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3772,plain,
% 7.69/1.51      ( k2_partfun1(sK5,sK3,sK7,X0_55) = k7_relat_1(sK7,X0_55)
% 7.69/1.51      | v1_funct_1(sK7) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1965,c_1960]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_25,negated_conjecture,
% 7.69/1.51      ( v1_funct_1(sK7) ),
% 7.69/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_46,plain,
% 7.69/1.51      ( v1_funct_1(sK7) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3868,plain,
% 7.69/1.51      ( k2_partfun1(sK5,sK3,sK7,X0_55) = k7_relat_1(sK7,X0_55) ),
% 7.69/1.51      inference(global_propositional_subsumption,[status(thm)],[c_3772,c_46]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_18,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3)
% 7.69/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X1)
% 7.69/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.69/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_21,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3)
% 7.69/1.51      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X1) ),
% 7.69/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_20,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3)
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X1) ),
% 7.69/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_19,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3)
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X1) ),
% 7.69/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_194,plain,
% 7.69/1.51      ( ~ v1_funct_1(X3)
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X1)
% 7.69/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_18,c_21,c_20,c_19]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_195,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3)
% 7.69/1.51      | v1_xboole_0(X1)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_194]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1128,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 7.69/1.51      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 7.69/1.51      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 7.69/1.51      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 7.69/1.51      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.69/1.51      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 7.69/1.51      | ~ v1_funct_1(X0_55)
% 7.69/1.51      | ~ v1_funct_1(X3_55)
% 7.69/1.51      | v1_xboole_0(X1_55)
% 7.69/1.51      | v1_xboole_0(X2_55)
% 7.69/1.51      | v1_xboole_0(X4_55)
% 7.69/1.51      | v1_xboole_0(X5_55)
% 7.69/1.51      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_195]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1977,plain,
% 7.69/1.51      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
% 7.69/1.51      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 7.69/1.51      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 7.69/1.51      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.69/1.51      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 7.69/1.51      | v1_funct_1(X2_55) != iProver_top
% 7.69/1.51      | v1_funct_1(X5_55) != iProver_top
% 7.69/1.51      | v1_xboole_0(X3_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X4_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X1_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4490,plain,
% 7.69/1.51      ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
% 7.69/1.51      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 7.69/1.51      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 7.69/1.51      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | v1_funct_1(X1_55) != iProver_top
% 7.69/1.51      | v1_funct_1(sK7) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X2_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(sK3) = iProver_top
% 7.69/1.51      | v1_xboole_0(sK5) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_3868,c_1977]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_34,negated_conjecture,
% 7.69/1.51      ( ~ v1_xboole_0(sK3) ),
% 7.69/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_37,plain,
% 7.69/1.51      ( v1_xboole_0(sK3) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_31,negated_conjecture,
% 7.69/1.51      ( ~ v1_xboole_0(sK5) ),
% 7.69/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_40,plain,
% 7.69/1.51      ( v1_xboole_0(sK5) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_24,negated_conjecture,
% 7.69/1.51      ( v1_funct_2(sK7,sK5,sK3) ),
% 7.69/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_47,plain,
% 7.69/1.51      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_48,plain,
% 7.69/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6106,plain,
% 7.69/1.51      ( v1_funct_1(X1_55) != iProver_top
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 7.69/1.51      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
% 7.69/1.51      | k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X2_55) = iProver_top ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_4490,c_37,c_40,c_46,c_47,c_48]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6107,plain,
% 7.69/1.51      ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),X0_55) = X1_55
% 7.69/1.51      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | v1_funct_1(X1_55) != iProver_top
% 7.69/1.51      | v1_xboole_0(X2_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_6106]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6113,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.69/1.51      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 7.69/1.51      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.69/1.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | v1_funct_1(sK6) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_3873,c_6107]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_33,negated_conjecture,
% 7.69/1.51      ( ~ v1_xboole_0(sK4) ),
% 7.69/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_38,plain,
% 7.69/1.51      ( v1_xboole_0(sK4) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_27,negated_conjecture,
% 7.69/1.51      ( v1_funct_2(sK6,sK4,sK3) ),
% 7.69/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_44,plain,
% 7.69/1.51      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_45,plain,
% 7.69/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6193,plain,
% 7.69/1.51      ( v1_xboole_0(X0_55) = iProver_top
% 7.69/1.51      | k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.69/1.51      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_6113,c_38,c_43,c_44,c_45]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6194,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.69/1.51      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_6193]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6199,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.69/1.51      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_2943,c_6194]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_12,plain,
% 7.69/1.51      ( ~ r1_subset_1(X0,X1)
% 7.69/1.51      | r1_xboole_0(X0,X1)
% 7.69/1.51      | v1_xboole_0(X0)
% 7.69/1.51      | v1_xboole_0(X1) ),
% 7.69/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_29,negated_conjecture,
% 7.69/1.51      ( r1_subset_1(sK4,sK5) ),
% 7.69/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_505,plain,
% 7.69/1.51      ( r1_xboole_0(X0,X1)
% 7.69/1.51      | v1_xboole_0(X0)
% 7.69/1.51      | v1_xboole_0(X1)
% 7.69/1.51      | sK5 != X1
% 7.69/1.51      | sK4 != X0 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_506,plain,
% 7.69/1.51      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_505]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_508,plain,
% 7.69/1.51      ( r1_xboole_0(sK4,sK5) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_506,c_33,c_31]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1125,plain,
% 7.69/1.51      ( r1_xboole_0(sK4,sK5) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_508]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1980,plain,
% 7.69/1.51      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3,plain,
% 7.69/1.51      ( ~ r1_xboole_0(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1154,plain,
% 7.69/1.51      ( ~ r1_xboole_0(X0_55,X1_55)
% 7.69/1.51      | k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1952,plain,
% 7.69/1.51      ( k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0
% 7.69/1.51      | r1_xboole_0(X0_55,X1_55) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2880,plain,
% 7.69/1.51      ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1980,c_1952]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6200,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.69/1.51      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_6199,c_2880]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6201,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.69/1.51      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0)
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_6200,c_2943]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6202,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.69/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_6201,c_2880]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_35,negated_conjecture,
% 7.69/1.51      ( ~ v1_xboole_0(sK2) ),
% 7.69/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_36,plain,
% 7.69/1.51      ( v1_xboole_0(sK2) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_32,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_39,plain,
% 7.69/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_41,plain,
% 7.69/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6203,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 7.69/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 7.69/1.51      | v1_xboole_0(sK2)
% 7.69/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.69/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.69/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_6202]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_14,plain,
% 7.69/1.51      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.69/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_10,plain,
% 7.69/1.51      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_466,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | k7_relat_1(X0,X1) = X0 ),
% 7.69/1.51      inference(resolution,[status(thm)],[c_14,c_10]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_13,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_470,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | k7_relat_1(X0,X1) = X0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_466,c_14,c_13,c_10]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1126,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.69/1.51      | k7_relat_1(X0_55,X1_55) = X0_55 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_470]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1979,plain,
% 7.69/1.51      ( k7_relat_1(X0_55,X1_55) = X0_55
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6789,plain,
% 7.69/1.51      ( k7_relat_1(sK7,sK5) = sK7 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1965,c_1979]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1147,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.69/1.51      | v1_relat_1(X0_55) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_13]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1959,plain,
% 7.69/1.51      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_55) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1147]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3048,plain,
% 7.69/1.51      ( v1_relat_1(sK7) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1965,c_1959]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4,plain,
% 7.69/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1153,plain,
% 7.69/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_4]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1953,plain,
% 7.69/1.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6,plain,
% 7.69/1.51      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.69/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1151,plain,
% 7.69/1.51      ( r1_xboole_0(X0_55,X1_55) | r2_hidden(sK1(X0_55,X1_55),X1_55) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_6]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1955,plain,
% 7.69/1.51      ( r1_xboole_0(X0_55,X1_55) = iProver_top
% 7.69/1.51      | r2_hidden(sK1(X0_55,X1_55),X1_55) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1,plain,
% 7.69/1.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.69/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1156,plain,
% 7.69/1.51      ( ~ r2_hidden(X0_58,X0_55) | ~ v1_xboole_0(X0_55) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_1]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1950,plain,
% 7.69/1.51      ( r2_hidden(X0_58,X0_55) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2950,plain,
% 7.69/1.51      ( r1_xboole_0(X0_55,X1_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X1_55) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1955,c_1950]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4178,plain,
% 7.69/1.51      ( k1_setfam_1(k2_tarski(X0_55,X1_55)) = k1_xboole_0
% 7.69/1.51      | v1_xboole_0(X1_55) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_2950,c_1952]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4622,plain,
% 7.69/1.51      ( k1_setfam_1(k2_tarski(X0_55,k1_xboole_0)) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1953,c_4178]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2,plain,
% 7.69/1.51      ( r1_xboole_0(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1155,plain,
% 7.69/1.51      ( r1_xboole_0(X0_55,X1_55)
% 7.69/1.51      | k1_setfam_1(k2_tarski(X0_55,X1_55)) != k1_xboole_0 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1951,plain,
% 7.69/1.51      ( k1_setfam_1(k2_tarski(X0_55,X1_55)) != k1_xboole_0
% 7.69/1.51      | r1_xboole_0(X0_55,X1_55) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4624,plain,
% 7.69/1.51      ( r1_xboole_0(X0_55,k1_xboole_0) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_4622,c_1951]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_9,plain,
% 7.69/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.69/1.51      | ~ v1_relat_1(X2)
% 7.69/1.51      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1148,plain,
% 7.69/1.51      ( ~ r1_xboole_0(X0_55,X1_55)
% 7.69/1.51      | ~ v1_relat_1(X2_55)
% 7.69/1.51      | k7_relat_1(k7_relat_1(X2_55,X0_55),X1_55) = k1_xboole_0 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_9]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1958,plain,
% 7.69/1.51      ( k7_relat_1(k7_relat_1(X0_55,X1_55),X2_55) = k1_xboole_0
% 7.69/1.51      | r1_xboole_0(X1_55,X2_55) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_55) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_5409,plain,
% 7.69/1.51      ( k7_relat_1(k7_relat_1(X0_55,X1_55),k1_xboole_0) = k1_xboole_0
% 7.69/1.51      | v1_relat_1(X0_55) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_4624,c_1958]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6871,plain,
% 7.69/1.51      ( k7_relat_1(k7_relat_1(sK7,X0_55),k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_3048,c_5409]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6948,plain,
% 7.69/1.51      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_6789,c_6871]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_22,negated_conjecture,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.69/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.69/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1141,negated_conjecture,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.69/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.69/1.51      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_22]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3199,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.69/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.69/1.51      | k2_partfun1(sK5,sK3,sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k2_partfun1(sK4,sK3,sK6,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_2943,c_1141]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3200,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.69/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.69/1.51      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_3199,c_2880]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3871,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.69/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.69/1.51      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_3868,c_3200]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4002,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.69/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.69/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_3871,c_3873]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6949,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.69/1.51      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.69/1.51      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_6948,c_4002]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6790,plain,
% 7.69/1.51      ( k7_relat_1(sK6,sK4) = sK6 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1968,c_1979]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3049,plain,
% 7.69/1.51      ( v1_relat_1(sK6) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1968,c_1959]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6872,plain,
% 7.69/1.51      ( k7_relat_1(k7_relat_1(sK6,X0_55),k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_3049,c_5409]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6966,plain,
% 7.69/1.51      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_6790,c_6872]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_17,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3)
% 7.69/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X1)
% 7.69/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_201,plain,
% 7.69/1.51      ( ~ v1_funct_1(X3)
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X1)
% 7.69/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_17,c_21,c_20,c_19]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_202,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.69/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3)
% 7.69/1.51      | v1_xboole_0(X1)
% 7.69/1.51      | v1_xboole_0(X2)
% 7.69/1.51      | v1_xboole_0(X4)
% 7.69/1.51      | v1_xboole_0(X5)
% 7.69/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_201]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1127,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 7.69/1.51      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 7.69/1.51      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 7.69/1.51      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 7.69/1.51      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.69/1.51      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 7.69/1.51      | ~ v1_funct_1(X0_55)
% 7.69/1.51      | ~ v1_funct_1(X3_55)
% 7.69/1.51      | v1_xboole_0(X1_55)
% 7.69/1.51      | v1_xboole_0(X2_55)
% 7.69/1.51      | v1_xboole_0(X4_55)
% 7.69/1.51      | v1_xboole_0(X5_55)
% 7.69/1.51      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_202]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1978,plain,
% 7.69/1.51      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
% 7.69/1.51      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 7.69/1.51      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 7.69/1.51      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.69/1.51      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 7.69/1.51      | v1_funct_1(X2_55) != iProver_top
% 7.69/1.51      | v1_funct_1(X5_55) != iProver_top
% 7.69/1.51      | v1_xboole_0(X3_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X4_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X1_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6379,plain,
% 7.69/1.51      ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
% 7.69/1.51      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 7.69/1.51      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 7.69/1.51      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | v1_funct_1(X1_55) != iProver_top
% 7.69/1.51      | v1_funct_1(sK7) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X2_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(sK3) = iProver_top
% 7.69/1.51      | v1_xboole_0(sK5) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_3868,c_1978]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7230,plain,
% 7.69/1.51      ( v1_funct_1(X1_55) != iProver_top
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 7.69/1.51      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
% 7.69/1.51      | k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X2_55) = iProver_top ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_6379,c_37,c_40,c_46,c_47,c_48]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7231,plain,
% 7.69/1.51      ( k2_partfun1(X0_55,sK3,X1_55,k9_subset_1(X2_55,X0_55,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_55,X0_55,sK5))
% 7.69/1.51      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK5),sK3,k1_tmap_1(X2_55,sK3,X0_55,sK5,X1_55,sK7),sK5) = sK7
% 7.69/1.51      | v1_funct_2(X1_55,X0_55,sK3) != iProver_top
% 7.69/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 7.69/1.51      | v1_funct_1(X1_55) != iProver_top
% 7.69/1.51      | v1_xboole_0(X2_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_7230]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7237,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.69/1.51      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 7.69/1.51      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.69/1.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | v1_funct_1(sK6) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top
% 7.69/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_3873,c_7231]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7272,plain,
% 7.69/1.51      ( v1_xboole_0(X0_55) = iProver_top
% 7.69/1.51      | k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.69/1.51      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_7237,c_38,c_43,c_44,c_45]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7273,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(X0_55,sK4,sK5),sK3,k1_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.69/1.51      | k7_relat_1(sK7,k9_subset_1(X0_55,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_55,sK4,sK5))
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0_55)) != iProver_top
% 7.69/1.51      | v1_xboole_0(X0_55) = iProver_top ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_7272]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7278,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.69/1.51      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5)))
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_2943,c_7273]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7279,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.69/1.51      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_7278,c_2880,c_6948]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7280,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.69/1.51      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k1_xboole_0
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_7279,c_2943]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7281,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.69/1.51      | k1_xboole_0 != k1_xboole_0
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_7280,c_2880,c_6966]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7282,plain,
% 7.69/1.51      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.69/1.51      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.69/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.69/1.51      inference(equality_resolution_simp,[status(thm)],[c_7281]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_11701,plain,
% 7.69/1.51      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_6202,c_35,c_36,c_32,c_39,c_30,c_41,c_6203,c_6949,c_6966,
% 7.69/1.51                 c_7282]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_11703,plain,
% 7.69/1.51      ( k1_xboole_0 != k1_xboole_0 ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_11701,c_6948,c_6966]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_11704,plain,
% 7.69/1.51      ( $false ),
% 7.69/1.51      inference(equality_resolution_simp,[status(thm)],[c_11703]) ).
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.69/1.51  
% 7.69/1.51  ------                               Statistics
% 7.69/1.51  
% 7.69/1.51  ------ General
% 7.69/1.51  
% 7.69/1.51  abstr_ref_over_cycles:                  0
% 7.69/1.51  abstr_ref_under_cycles:                 0
% 7.69/1.51  gc_basic_clause_elim:                   0
% 7.69/1.51  forced_gc_time:                         0
% 7.69/1.51  parsing_time:                           0.009
% 7.69/1.51  unif_index_cands_time:                  0.
% 7.69/1.51  unif_index_add_time:                    0.
% 7.69/1.51  orderings_time:                         0.
% 7.69/1.51  out_proof_time:                         0.016
% 7.69/1.51  total_time:                             0.788
% 7.69/1.51  num_of_symbols:                         62
% 7.69/1.51  num_of_terms:                           32922
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing
% 7.69/1.51  
% 7.69/1.51  num_of_splits:                          0
% 7.69/1.51  num_of_split_atoms:                     0
% 7.69/1.51  num_of_reused_defs:                     0
% 7.69/1.51  num_eq_ax_congr_red:                    28
% 7.69/1.51  num_of_sem_filtered_clauses:            1
% 7.69/1.51  num_of_subtypes:                        4
% 7.69/1.51  monotx_restored_types:                  0
% 7.69/1.51  sat_num_of_epr_types:                   0
% 7.69/1.51  sat_num_of_non_cyclic_types:            0
% 7.69/1.51  sat_guarded_non_collapsed_types:        1
% 7.69/1.51  num_pure_diseq_elim:                    0
% 7.69/1.51  simp_replaced_by:                       0
% 7.69/1.51  res_preprocessed:                       174
% 7.69/1.51  prep_upred:                             0
% 7.69/1.51  prep_unflattend:                        16
% 7.69/1.51  smt_new_axioms:                         0
% 7.69/1.51  pred_elim_cands:                        7
% 7.69/1.51  pred_elim:                              2
% 7.69/1.51  pred_elim_cl:                           3
% 7.69/1.51  pred_elim_cycles:                       6
% 7.69/1.51  merged_defs:                            8
% 7.69/1.51  merged_defs_ncl:                        0
% 7.69/1.51  bin_hyper_res:                          8
% 7.69/1.51  prep_cycles:                            4
% 7.69/1.51  pred_elim_time:                         0.008
% 7.69/1.51  splitting_time:                         0.
% 7.69/1.51  sem_filter_time:                        0.
% 7.69/1.51  monotx_time:                            0.
% 7.69/1.51  subtype_inf_time:                       0.001
% 7.69/1.51  
% 7.69/1.51  ------ Problem properties
% 7.69/1.51  
% 7.69/1.51  clauses:                                33
% 7.69/1.51  conjectures:                            13
% 7.69/1.51  epr:                                    12
% 7.69/1.51  horn:                                   24
% 7.69/1.51  ground:                                 15
% 7.69/1.51  unary:                                  14
% 7.69/1.51  binary:                                 9
% 7.69/1.51  lits:                                   128
% 7.69/1.51  lits_eq:                                15
% 7.69/1.51  fd_pure:                                0
% 7.69/1.51  fd_pseudo:                              0
% 7.69/1.51  fd_cond:                                0
% 7.69/1.51  fd_pseudo_cond:                         0
% 7.69/1.51  ac_symbols:                             0
% 7.69/1.51  
% 7.69/1.51  ------ Propositional Solver
% 7.69/1.51  
% 7.69/1.51  prop_solver_calls:                      30
% 7.69/1.51  prop_fast_solver_calls:                 3661
% 7.69/1.51  smt_solver_calls:                       0
% 7.69/1.51  smt_fast_solver_calls:                  0
% 7.69/1.51  prop_num_of_clauses:                    6515
% 7.69/1.51  prop_preprocess_simplified:             12333
% 7.69/1.51  prop_fo_subsumed:                       289
% 7.69/1.51  prop_solver_time:                       0.
% 7.69/1.51  smt_solver_time:                        0.
% 7.69/1.51  smt_fast_solver_time:                   0.
% 7.69/1.51  prop_fast_solver_time:                  0.
% 7.69/1.51  prop_unsat_core_time:                   0.
% 7.69/1.51  
% 7.69/1.51  ------ QBF
% 7.69/1.51  
% 7.69/1.51  qbf_q_res:                              0
% 7.69/1.51  qbf_num_tautologies:                    0
% 7.69/1.51  qbf_prep_cycles:                        0
% 7.69/1.51  
% 7.69/1.51  ------ BMC1
% 7.69/1.51  
% 7.69/1.51  bmc1_current_bound:                     -1
% 7.69/1.51  bmc1_last_solved_bound:                 -1
% 7.69/1.51  bmc1_unsat_core_size:                   -1
% 7.69/1.51  bmc1_unsat_core_parents_size:           -1
% 7.69/1.51  bmc1_merge_next_fun:                    0
% 7.69/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.69/1.51  
% 7.69/1.51  ------ Instantiation
% 7.69/1.51  
% 7.69/1.51  inst_num_of_clauses:                    1367
% 7.69/1.51  inst_num_in_passive:                    180
% 7.69/1.51  inst_num_in_active:                     897
% 7.69/1.51  inst_num_in_unprocessed:                290
% 7.69/1.51  inst_num_of_loops:                      1020
% 7.69/1.51  inst_num_of_learning_restarts:          0
% 7.69/1.51  inst_num_moves_active_passive:          120
% 7.69/1.51  inst_lit_activity:                      0
% 7.69/1.51  inst_lit_activity_moves:                1
% 7.69/1.51  inst_num_tautologies:                   0
% 7.69/1.51  inst_num_prop_implied:                  0
% 7.69/1.51  inst_num_existing_simplified:           0
% 7.69/1.51  inst_num_eq_res_simplified:             0
% 7.69/1.51  inst_num_child_elim:                    0
% 7.69/1.51  inst_num_of_dismatching_blockings:      267
% 7.69/1.51  inst_num_of_non_proper_insts:           1531
% 7.69/1.51  inst_num_of_duplicates:                 0
% 7.69/1.51  inst_inst_num_from_inst_to_res:         0
% 7.69/1.51  inst_dismatching_checking_time:         0.
% 7.69/1.51  
% 7.69/1.51  ------ Resolution
% 7.69/1.51  
% 7.69/1.51  res_num_of_clauses:                     0
% 7.69/1.51  res_num_in_passive:                     0
% 7.69/1.51  res_num_in_active:                      0
% 7.69/1.51  res_num_of_loops:                       178
% 7.69/1.51  res_forward_subset_subsumed:            24
% 7.69/1.51  res_backward_subset_subsumed:           0
% 7.69/1.51  res_forward_subsumed:                   0
% 7.69/1.51  res_backward_subsumed:                  0
% 7.69/1.51  res_forward_subsumption_resolution:     0
% 7.69/1.51  res_backward_subsumption_resolution:    0
% 7.69/1.51  res_clause_to_clause_subsumption:       919
% 7.69/1.51  res_orphan_elimination:                 0
% 7.69/1.51  res_tautology_del:                      28
% 7.69/1.51  res_num_eq_res_simplified:              0
% 7.69/1.51  res_num_sel_changes:                    0
% 7.69/1.51  res_moves_from_active_to_pass:          0
% 7.69/1.51  
% 7.69/1.51  ------ Superposition
% 7.69/1.51  
% 7.69/1.51  sup_time_total:                         0.
% 7.69/1.51  sup_time_generating:                    0.
% 7.69/1.51  sup_time_sim_full:                      0.
% 7.69/1.51  sup_time_sim_immed:                     0.
% 7.69/1.51  
% 7.69/1.51  sup_num_of_clauses:                     336
% 7.69/1.51  sup_num_in_active:                      184
% 7.69/1.51  sup_num_in_passive:                     152
% 7.69/1.51  sup_num_of_loops:                       202
% 7.69/1.51  sup_fw_superposition:                   274
% 7.69/1.51  sup_bw_superposition:                   142
% 7.69/1.51  sup_immediate_simplified:               170
% 7.69/1.51  sup_given_eliminated:                   0
% 7.69/1.51  comparisons_done:                       0
% 7.69/1.51  comparisons_avoided:                    0
% 7.69/1.51  
% 7.69/1.51  ------ Simplifications
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  sim_fw_subset_subsumed:                 28
% 7.69/1.51  sim_bw_subset_subsumed:                 0
% 7.69/1.51  sim_fw_subsumed:                        17
% 7.69/1.51  sim_bw_subsumed:                        11
% 7.69/1.51  sim_fw_subsumption_res:                 0
% 7.69/1.51  sim_bw_subsumption_res:                 0
% 7.69/1.51  sim_tautology_del:                      1
% 7.69/1.51  sim_eq_tautology_del:                   8
% 7.69/1.51  sim_eq_res_simp:                        4
% 7.69/1.51  sim_fw_demodulated:                     85
% 7.69/1.51  sim_bw_demodulated:                     7
% 7.69/1.51  sim_light_normalised:                   68
% 7.69/1.51  sim_joinable_taut:                      0
% 7.69/1.51  sim_joinable_simp:                      0
% 7.69/1.51  sim_ac_normalised:                      0
% 7.69/1.51  sim_smt_subsumption:                    0
% 7.69/1.51  
%------------------------------------------------------------------------------
