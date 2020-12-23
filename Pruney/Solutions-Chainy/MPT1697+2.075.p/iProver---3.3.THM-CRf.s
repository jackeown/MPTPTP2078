%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:39 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 776 expanded)
%              Number of clauses        :  125 ( 220 expanded)
%              Number of leaves         :   25 ( 278 expanded)
%              Depth                    :   23
%              Number of atoms          : 1110 (8886 expanded)
%              Number of equality atoms :  249 (1993 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f43,f60,f59,f58,f57,f56,f55])).

fof(f103,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f61])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f93,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f95,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f100,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f61])).

fof(f104,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f102,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f53,plain,(
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

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f112,plain,(
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
    inference(equality_resolution,[],[f85])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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

fof(f88,plain,(
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

fof(f89,plain,(
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

fof(f90,plain,(
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

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,(
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
    inference(equality_resolution,[],[f86])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_947,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1908,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1900,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
    | v1_relat_1(X1_57) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_2868,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK3)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1900])).

cnf(c_2485,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK3))
    | v1_relat_1(sK7) ),
    inference(resolution,[status(thm)],[c_956,c_947])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_955,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2559,plain,
    ( v1_relat_1(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2485,c_955])).

cnf(c_2560,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2559])).

cnf(c_4641,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2868,c_2560])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_963,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1893,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_960,plain,
    ( r1_xboole_0(X0_57,X1_57)
    | r2_hidden(sK1(X0_57,X1_57),X1_57) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1896,plain,
    ( r1_xboole_0(X0_57,X1_57) = iProver_top
    | r2_hidden(sK1(X0_57,X1_57),X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_966,plain,
    ( ~ r2_hidden(X0_60,X0_57)
    | ~ v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1890,plain,
    ( r2_hidden(X0_60,X0_57) != iProver_top
    | v1_xboole_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_966])).

cnf(c_2789,plain,
    ( r1_xboole_0(X0_57,X1_57) = iProver_top
    | v1_xboole_0(X1_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_1890])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_964,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1892,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(c_3851,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
    | v1_xboole_0(X1_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_2789,c_1892])).

cnf(c_4766,plain,
    ( k1_setfam_1(k2_tarski(X0_57,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1893,c_3851])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_965,plain,
    ( r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1891,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) != k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_4768,plain,
    ( r1_xboole_0(X0_57,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4766,c_1891])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_962,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | r1_xboole_0(X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1894,plain,
    ( r1_xboole_0(X0_57,X1_57) != iProver_top
    | r1_xboole_0(X1_57,X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_5079,plain,
    ( r1_xboole_0(k1_xboole_0,X0_57) = iProver_top ),
    inference(superposition,[status(thm)],[c_4768,c_1894])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_954,plain,
    ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1902,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_5090,plain,
    ( k7_relat_1(X0_57,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_5079,c_1902])).

cnf(c_5738,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4641,c_5090])).

cnf(c_15,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_569,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_35])).

cnf(c_570,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_572,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_39,c_37])).

cnf(c_933,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_572])).

cnf(c_1922,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_4137,plain,
    ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1922,c_1892])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_941,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1914,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_958,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1898,plain,
    ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_2473,plain,
    ( k9_subset_1(sK2,X0_57,sK5) = k1_setfam_1(k2_tarski(X0_57,sK5)) ),
    inference(superposition,[status(thm)],[c_1914,c_1898])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_944,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1911,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_953,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1903,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_2878,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_1903])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2149,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0_57,X1_57,sK6,X2_57) = k7_relat_1(sK6,X2_57) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_2352,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_5572,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2878,c_34,c_32,c_2352])).

cnf(c_2877,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1903])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2144,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0_57,X1_57,sK7,X2_57) = k7_relat_1(sK7,X2_57) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_2347,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_4846,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2877,c_31,c_29,c_2347])).

cnf(c_28,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_948,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_4849,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_4846,c_948])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_973,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_2090,plain,
    ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != X0_57
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != X0_57
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_2274,plain,
    ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_969,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_2275,plain,
    ( k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_2544,plain,
    ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != X0_57
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != X0_57 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_3510,plain,
    ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5))
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2544])).

cnf(c_3511,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f112])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f88])).

cnf(c_26,plain,
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
    inference(cnf_transformation,[],[f89])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f90])).

cnf(c_222,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_27,c_26,c_25])).

cnf(c_223,plain,
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
    inference(renaming,[status(thm)],[c_222])).

cnf(c_935,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X3_57,X4_57,X2_57)
    | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X3_57)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X5_57)
    | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
    | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
    inference(subtyping,[status(esa)],[c_223])).

cnf(c_2231,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(sK6,X3_57,X2_57)
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X3_57)
    | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X4_57,X3_57,X1_57)) != k2_partfun1(X3_57,X2_57,sK6,k9_subset_1(X4_57,X3_57,X1_57))
    | k2_partfun1(k4_subset_1(X4_57,X3_57,X1_57),X2_57,k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK6,X0_57),X3_57) = sK6 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_2461,plain,
    ( ~ v1_funct_2(sK7,X0_57,X1_57)
    | ~ v1_funct_2(sK6,X2_57,X1_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
    | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X3_57)
    | v1_xboole_0(X0_57)
    | k2_partfun1(X0_57,X1_57,sK7,k9_subset_1(X3_57,X2_57,X0_57)) != k2_partfun1(X2_57,X1_57,sK6,k9_subset_1(X3_57,X2_57,X0_57))
    | k2_partfun1(k4_subset_1(X3_57,X2_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK6,sK7),X2_57) = sK6 ),
    inference(instantiation,[status(thm)],[c_2231])).

cnf(c_2941,plain,
    ( ~ v1_funct_2(sK7,X0_57,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X1_57))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK4)
    | k2_partfun1(X0_57,sK3,sK7,k9_subset_1(X1_57,sK4,X0_57)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X1_57,sK4,X0_57))
    | k2_partfun1(k4_subset_1(X1_57,sK4,X0_57),sK3,k1_tmap_1(X1_57,sK3,sK4,X0_57,sK6,sK7),sK4) = sK6 ),
    inference(instantiation,[status(thm)],[c_2461])).

cnf(c_3362,plain,
    ( ~ v1_funct_2(sK7,sK5,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0_57))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0_57))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X0_57)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(X0_57,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X0_57,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2941])).

cnf(c_4587,plain,
    ( ~ v1_funct_2(sK7,sK5,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3362])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f111])).

cnf(c_229,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_27,c_26,c_25])).

cnf(c_230,plain,
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
    inference(renaming,[status(thm)],[c_229])).

cnf(c_934,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X3_57,X4_57,X2_57)
    | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X3_57)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X5_57)
    | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
    | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_230])).

cnf(c_2221,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(sK6,X3_57,X2_57)
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X3_57)
    | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X4_57,X3_57,X1_57)) != k2_partfun1(X3_57,X2_57,sK6,k9_subset_1(X4_57,X3_57,X1_57))
    | k2_partfun1(k4_subset_1(X4_57,X3_57,X1_57),X2_57,k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK6,X0_57),X1_57) = X0_57 ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_2521,plain,
    ( ~ v1_funct_2(sK7,X0_57,X1_57)
    | ~ v1_funct_2(sK6,X2_57,X1_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
    | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X3_57)
    | v1_xboole_0(X0_57)
    | k2_partfun1(X0_57,X1_57,sK7,k9_subset_1(X3_57,X2_57,X0_57)) != k2_partfun1(X2_57,X1_57,sK6,k9_subset_1(X3_57,X2_57,X0_57))
    | k2_partfun1(k4_subset_1(X3_57,X2_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK6,sK7),X0_57) = sK7 ),
    inference(instantiation,[status(thm)],[c_2221])).

cnf(c_2969,plain,
    ( ~ v1_funct_2(sK7,X0_57,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X1_57))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK4)
    | k2_partfun1(X0_57,sK3,sK7,k9_subset_1(X1_57,sK4,X0_57)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X1_57,sK4,X0_57))
    | k2_partfun1(k4_subset_1(X1_57,sK4,X0_57),sK3,k1_tmap_1(X1_57,sK3,sK4,X0_57,sK6,sK7),X0_57) = sK7 ),
    inference(instantiation,[status(thm)],[c_2521])).

cnf(c_3383,plain,
    ( ~ v1_funct_2(sK7,sK5,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0_57))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0_57))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(X0_57)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(X0_57,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X0_57,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2969])).

cnf(c_4599,plain,
    ( ~ v1_funct_2(sK7,sK5,sK3)
    | ~ v1_funct_2(sK6,sK4,sK3)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3383])).

cnf(c_4867,plain,
    ( k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4849,c_41,c_40,c_39,c_38,c_37,c_36,c_34,c_33,c_32,c_31,c_30,c_29,c_948,c_2274,c_2275,c_3510,c_3511,c_4587,c_4599])).

cnf(c_5575,plain,
    ( k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_5572,c_4867])).

cnf(c_8700,plain,
    ( k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_2473,c_5575])).

cnf(c_8915,plain,
    ( k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4137,c_8700])).

cnf(c_8916,plain,
    ( k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2473,c_8915])).

cnf(c_9152,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4137,c_8916])).

cnf(c_9297,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5738,c_9152])).

cnf(c_2869,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK3)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_1900])).

cnf(c_2487,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK3))
    | v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_956,c_944])).

cnf(c_2566,plain,
    ( v1_relat_1(sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2487,c_955])).

cnf(c_2567,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2566])).

cnf(c_4646,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2869,c_2567])).

cnf(c_5739,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4646,c_5090])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9297,c_5739])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:31:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.90/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/0.98  
% 3.90/0.98  ------  iProver source info
% 3.90/0.98  
% 3.90/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.90/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/0.98  git: non_committed_changes: false
% 3.90/0.98  git: last_make_outside_of_git: false
% 3.90/0.98  
% 3.90/0.98  ------ 
% 3.90/0.98  ------ Parsing...
% 3.90/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.98  ------ Proving...
% 3.90/0.98  ------ Problem Properties 
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  clauses                                 36
% 3.90/0.98  conjectures                             13
% 3.90/0.98  EPR                                     13
% 3.90/0.98  Horn                                    26
% 3.90/0.98  unary                                   15
% 3.90/0.98  binary                                  8
% 3.90/0.98  lits                                    139
% 3.90/0.98  lits eq                                 15
% 3.90/0.98  fd_pure                                 0
% 3.90/0.98  fd_pseudo                               0
% 3.90/0.98  fd_cond                                 0
% 3.90/0.98  fd_pseudo_cond                          1
% 3.90/0.98  AC symbols                              0
% 3.90/0.98  
% 3.90/0.98  ------ Input Options Time Limit: Unbounded
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  ------ 
% 3.90/0.98  Current options:
% 3.90/0.98  ------ 
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  ------ Proving...
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  % SZS status Theorem for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  fof(f19,conjecture,(
% 3.90/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f20,negated_conjecture,(
% 3.90/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.90/0.98    inference(negated_conjecture,[],[f19])).
% 3.90/0.98  
% 3.90/0.98  fof(f42,plain,(
% 3.90/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f20])).
% 3.90/0.98  
% 3.90/0.98  fof(f43,plain,(
% 3.90/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.90/0.98    inference(flattening,[],[f42])).
% 3.90/0.98  
% 3.90/0.98  fof(f60,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f59,plain,(
% 3.90/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f58,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f57,plain,(
% 3.90/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f56,plain,(
% 3.90/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f55,plain,(
% 3.90/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f61,plain,(
% 3.90/0.98    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f43,f60,f59,f58,f57,f56,f55])).
% 3.90/0.98  
% 3.90/0.98  fof(f103,plain,(
% 3.90/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f9,axiom,(
% 3.90/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f27,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f9])).
% 3.90/0.98  
% 3.90/0.98  fof(f74,plain,(
% 3.90/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f27])).
% 3.90/0.98  
% 3.90/0.98  fof(f10,axiom,(
% 3.90/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f75,plain,(
% 3.90/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f10])).
% 3.90/0.98  
% 3.90/0.98  fof(f3,axiom,(
% 3.90/0.98    v1_xboole_0(k1_xboole_0)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f66,plain,(
% 3.90/0.98    v1_xboole_0(k1_xboole_0)),
% 3.90/0.98    inference(cnf_transformation,[],[f3])).
% 3.90/0.98  
% 3.90/0.98  fof(f5,axiom,(
% 3.90/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f21,plain,(
% 3.90/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.90/0.98    inference(rectify,[],[f5])).
% 3.90/0.98  
% 3.90/0.98  fof(f24,plain,(
% 3.90/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.90/0.98    inference(ennf_transformation,[],[f21])).
% 3.90/0.98  
% 3.90/0.98  fof(f49,plain,(
% 3.90/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f50,plain,(
% 3.90/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f49])).
% 3.90/0.98  
% 3.90/0.98  fof(f69,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f50])).
% 3.90/0.98  
% 3.90/0.98  fof(f1,axiom,(
% 3.90/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f44,plain,(
% 3.90/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.90/0.98    inference(nnf_transformation,[],[f1])).
% 3.90/0.98  
% 3.90/0.98  fof(f45,plain,(
% 3.90/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.90/0.98    inference(rectify,[],[f44])).
% 3.90/0.98  
% 3.90/0.98  fof(f46,plain,(
% 3.90/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f47,plain,(
% 3.90/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 3.90/0.98  
% 3.90/0.98  fof(f62,plain,(
% 3.90/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f47])).
% 3.90/0.98  
% 3.90/0.98  fof(f2,axiom,(
% 3.90/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f48,plain,(
% 3.90/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.90/0.98    inference(nnf_transformation,[],[f2])).
% 3.90/0.98  
% 3.90/0.98  fof(f64,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f48])).
% 3.90/0.98  
% 3.90/0.98  fof(f8,axiom,(
% 3.90/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f73,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f8])).
% 3.90/0.98  
% 3.90/0.98  fof(f106,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f64,f73])).
% 3.90/0.98  
% 3.90/0.98  fof(f65,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.90/0.98    inference(cnf_transformation,[],[f48])).
% 3.90/0.98  
% 3.90/0.98  fof(f105,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.90/0.98    inference(definition_unfolding,[],[f65,f73])).
% 3.90/0.98  
% 3.90/0.98  fof(f4,axiom,(
% 3.90/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f23,plain,(
% 3.90/0.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.90/0.98    inference(ennf_transformation,[],[f4])).
% 3.90/0.98  
% 3.90/0.98  fof(f67,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f23])).
% 3.90/0.98  
% 3.90/0.98  fof(f11,axiom,(
% 3.90/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f28,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f11])).
% 3.90/0.98  
% 3.90/0.98  fof(f76,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f28])).
% 3.90/0.98  
% 3.90/0.98  fof(f12,axiom,(
% 3.90/0.98    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f29,plain,(
% 3.90/0.98    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f12])).
% 3.90/0.98  
% 3.90/0.98  fof(f30,plain,(
% 3.90/0.98    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.90/0.98    inference(flattening,[],[f29])).
% 3.90/0.98  
% 3.90/0.98  fof(f51,plain,(
% 3.90/0.98    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.90/0.98    inference(nnf_transformation,[],[f30])).
% 3.90/0.98  
% 3.90/0.98  fof(f77,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f51])).
% 3.90/0.98  
% 3.90/0.98  fof(f97,plain,(
% 3.90/0.98    r1_subset_1(sK4,sK5)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f93,plain,(
% 3.90/0.98    ~v1_xboole_0(sK4)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f95,plain,(
% 3.90/0.98    ~v1_xboole_0(sK5)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f96,plain,(
% 3.90/0.98    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f6,axiom,(
% 3.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f25,plain,(
% 3.90/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f6])).
% 3.90/0.98  
% 3.90/0.98  fof(f71,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f25])).
% 3.90/0.98  
% 3.90/0.98  fof(f107,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.90/0.98    inference(definition_unfolding,[],[f71,f73])).
% 3.90/0.98  
% 3.90/0.98  fof(f100,plain,(
% 3.90/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f16,axiom,(
% 3.90/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f36,plain,(
% 3.90/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.90/0.98    inference(ennf_transformation,[],[f16])).
% 3.90/0.98  
% 3.90/0.98  fof(f37,plain,(
% 3.90/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.90/0.98    inference(flattening,[],[f36])).
% 3.90/0.98  
% 3.90/0.98  fof(f84,plain,(
% 3.90/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f37])).
% 3.90/0.98  
% 3.90/0.98  fof(f98,plain,(
% 3.90/0.98    v1_funct_1(sK6)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f101,plain,(
% 3.90/0.98    v1_funct_1(sK7)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f104,plain,(
% 3.90/0.98    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f91,plain,(
% 3.90/0.98    ~v1_xboole_0(sK2)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f92,plain,(
% 3.90/0.98    ~v1_xboole_0(sK3)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f94,plain,(
% 3.90/0.98    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f99,plain,(
% 3.90/0.98    v1_funct_2(sK6,sK4,sK3)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f102,plain,(
% 3.90/0.98    v1_funct_2(sK7,sK5,sK3)),
% 3.90/0.98    inference(cnf_transformation,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f17,axiom,(
% 3.90/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f38,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f17])).
% 3.90/0.98  
% 3.90/0.98  fof(f39,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.90/0.98    inference(flattening,[],[f38])).
% 3.90/0.98  
% 3.90/0.98  fof(f53,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.90/0.98    inference(nnf_transformation,[],[f39])).
% 3.90/0.98  
% 3.90/0.98  fof(f54,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.90/0.98    inference(flattening,[],[f53])).
% 3.90/0.98  
% 3.90/0.98  fof(f85,plain,(
% 3.90/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f54])).
% 3.90/0.98  
% 3.90/0.98  fof(f112,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(equality_resolution,[],[f85])).
% 3.90/0.98  
% 3.90/0.98  fof(f18,axiom,(
% 3.90/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f40,plain,(
% 3.90/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f18])).
% 3.90/0.98  
% 3.90/0.98  fof(f41,plain,(
% 3.90/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.90/0.98    inference(flattening,[],[f40])).
% 3.90/0.98  
% 3.90/0.98  fof(f88,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f41])).
% 3.90/0.98  
% 3.90/0.98  fof(f89,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f41])).
% 3.90/0.98  
% 3.90/0.98  fof(f90,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f41])).
% 3.90/0.98  
% 3.90/0.98  fof(f86,plain,(
% 3.90/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f54])).
% 3.90/0.98  
% 3.90/0.98  fof(f111,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(equality_resolution,[],[f86])).
% 3.90/0.98  
% 3.90/0.98  cnf(c_29,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 3.90/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_947,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_29]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1908,plain,
% 3.90/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/0.98      | ~ v1_relat_1(X1)
% 3.90/0.98      | v1_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_956,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 3.90/0.98      | ~ v1_relat_1(X1_57)
% 3.90/0.98      | v1_relat_1(X0_57) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1900,plain,
% 3.90/0.98      ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
% 3.90/0.98      | v1_relat_1(X1_57) != iProver_top
% 3.90/0.98      | v1_relat_1(X0_57) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2868,plain,
% 3.90/0.98      ( v1_relat_1(k2_zfmisc_1(sK5,sK3)) != iProver_top
% 3.90/0.98      | v1_relat_1(sK7) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1908,c_1900]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2485,plain,
% 3.90/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK3)) | v1_relat_1(sK7) ),
% 3.90/0.98      inference(resolution,[status(thm)],[c_956,c_947]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_12,plain,
% 3.90/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_955,plain,
% 3.90/0.98      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2559,plain,
% 3.90/0.98      ( v1_relat_1(sK7) ),
% 3.90/0.98      inference(forward_subsumption_resolution,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_2485,c_955]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2560,plain,
% 3.90/0.98      ( v1_relat_1(sK7) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_2559]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4641,plain,
% 3.90/0.98      ( v1_relat_1(sK7) = iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_2868,c_2560]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4,plain,
% 3.90/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_963,plain,
% 3.90/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1893,plain,
% 3.90/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_7,plain,
% 3.90/0.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_960,plain,
% 3.90/0.98      ( r1_xboole_0(X0_57,X1_57) | r2_hidden(sK1(X0_57,X1_57),X1_57) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1896,plain,
% 3.90/0.98      ( r1_xboole_0(X0_57,X1_57) = iProver_top
% 3.90/0.98      | r2_hidden(sK1(X0_57,X1_57),X1_57) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_960]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1,plain,
% 3.90/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_966,plain,
% 3.90/0.98      ( ~ r2_hidden(X0_60,X0_57) | ~ v1_xboole_0(X0_57) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1890,plain,
% 3.90/0.98      ( r2_hidden(X0_60,X0_57) != iProver_top
% 3.90/0.98      | v1_xboole_0(X0_57) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_966]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2789,plain,
% 3.90/0.98      ( r1_xboole_0(X0_57,X1_57) = iProver_top
% 3.90/0.98      | v1_xboole_0(X1_57) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1896,c_1890]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3,plain,
% 3.90/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.90/0.98      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_964,plain,
% 3.90/0.98      ( ~ r1_xboole_0(X0_57,X1_57)
% 3.90/0.98      | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1892,plain,
% 3.90/0.98      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
% 3.90/0.98      | r1_xboole_0(X0_57,X1_57) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_964]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3851,plain,
% 3.90/0.98      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
% 3.90/0.98      | v1_xboole_0(X1_57) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2789,c_1892]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4766,plain,
% 3.90/0.98      ( k1_setfam_1(k2_tarski(X0_57,k1_xboole_0)) = k1_xboole_0 ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1893,c_3851]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2,plain,
% 3.90/0.98      ( r1_xboole_0(X0,X1)
% 3.90/0.98      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_965,plain,
% 3.90/0.98      ( r1_xboole_0(X0_57,X1_57)
% 3.90/0.98      | k1_setfam_1(k2_tarski(X0_57,X1_57)) != k1_xboole_0 ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1891,plain,
% 3.90/0.98      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) != k1_xboole_0
% 3.90/0.98      | r1_xboole_0(X0_57,X1_57) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4768,plain,
% 3.90/0.98      ( r1_xboole_0(X0_57,k1_xboole_0) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4766,c_1891]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5,plain,
% 3.90/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_962,plain,
% 3.90/0.98      ( ~ r1_xboole_0(X0_57,X1_57) | r1_xboole_0(X1_57,X0_57) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1894,plain,
% 3.90/0.98      ( r1_xboole_0(X0_57,X1_57) != iProver_top
% 3.90/0.98      | r1_xboole_0(X1_57,X0_57) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5079,plain,
% 3.90/0.98      ( r1_xboole_0(k1_xboole_0,X0_57) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4768,c_1894]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13,plain,
% 3.90/0.98      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 3.90/0.98      | ~ v1_relat_1(X1)
% 3.90/0.98      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_954,plain,
% 3.90/0.98      ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
% 3.90/0.98      | ~ v1_relat_1(X1_57)
% 3.90/0.98      | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1902,plain,
% 3.90/0.98      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 3.90/0.98      | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
% 3.90/0.98      | v1_relat_1(X0_57) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5090,plain,
% 3.90/0.98      ( k7_relat_1(X0_57,k1_xboole_0) = k1_xboole_0
% 3.90/0.98      | v1_relat_1(X0_57) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_5079,c_1902]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5738,plain,
% 3.90/0.98      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4641,c_5090]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15,plain,
% 3.90/0.98      ( ~ r1_subset_1(X0,X1)
% 3.90/0.98      | r1_xboole_0(X0,X1)
% 3.90/0.98      | v1_xboole_0(X0)
% 3.90/0.98      | v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_35,negated_conjecture,
% 3.90/0.98      ( r1_subset_1(sK4,sK5) ),
% 3.90/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_569,plain,
% 3.90/0.98      ( r1_xboole_0(X0,X1)
% 3.90/0.98      | v1_xboole_0(X0)
% 3.90/0.98      | v1_xboole_0(X1)
% 3.90/0.98      | sK5 != X1
% 3.90/0.98      | sK4 != X0 ),
% 3.90/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_35]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_570,plain,
% 3.90/0.98      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 3.90/0.98      inference(unflattening,[status(thm)],[c_569]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_39,negated_conjecture,
% 3.90/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.90/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_37,negated_conjecture,
% 3.90/0.98      ( ~ v1_xboole_0(sK5) ),
% 3.90/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_572,plain,
% 3.90/0.98      ( r1_xboole_0(sK4,sK5) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_570,c_39,c_37]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_933,plain,
% 3.90/0.98      ( r1_xboole_0(sK4,sK5) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_572]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1922,plain,
% 3.90/0.98      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4137,plain,
% 3.90/0.98      ( k1_setfam_1(k2_tarski(sK4,sK5)) = k1_xboole_0 ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1922,c_1892]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_36,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_941,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_36]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1914,plain,
% 3.90/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_9,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_958,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 3.90/0.98      | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1898,plain,
% 3.90/0.98      ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
% 3.90/0.98      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2473,plain,
% 3.90/0.98      ( k9_subset_1(sK2,X0_57,sK5) = k1_setfam_1(k2_tarski(X0_57,sK5)) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1914,c_1898]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_32,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.90/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_944,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_32]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1911,plain,
% 3.90/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_21,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.90/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_953,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 3.90/0.98      | ~ v1_funct_1(X0_57)
% 3.90/0.98      | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1903,plain,
% 3.90/0.98      ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
% 3.90/0.98      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.90/0.98      | v1_funct_1(X2_57) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2878,plain,
% 3.90/0.98      ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57)
% 3.90/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1911,c_1903]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_34,negated_conjecture,
% 3.90/0.98      ( v1_funct_1(sK6) ),
% 3.90/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2149,plain,
% 3.90/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | k2_partfun1(X0_57,X1_57,sK6,X2_57) = k7_relat_1(sK6,X2_57) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_953]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2352,plain,
% 3.90/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2149]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5572,plain,
% 3.90/0.98      ( k2_partfun1(sK4,sK3,sK6,X0_57) = k7_relat_1(sK6,X0_57) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_2878,c_34,c_32,c_2352]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2877,plain,
% 3.90/0.98      ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57)
% 3.90/0.98      | v1_funct_1(sK7) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1908,c_1903]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_31,negated_conjecture,
% 3.90/0.98      ( v1_funct_1(sK7) ),
% 3.90/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2144,plain,
% 3.90/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | k2_partfun1(X0_57,X1_57,sK7,X2_57) = k7_relat_1(sK7,X2_57) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_953]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2347,plain,
% 3.90/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2144]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4846,plain,
% 3.90/0.98      ( k2_partfun1(sK5,sK3,sK7,X0_57) = k7_relat_1(sK7,X0_57) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_2877,c_31,c_29,c_2347]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_28,negated_conjecture,
% 3.90/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.90/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_948,negated_conjecture,
% 3.90/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.90/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_28]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4849,plain,
% 3.90/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.90/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4846,c_948]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_41,negated_conjecture,
% 3.90/0.98      ( ~ v1_xboole_0(sK2) ),
% 3.90/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_40,negated_conjecture,
% 3.90/0.98      ( ~ v1_xboole_0(sK3) ),
% 3.90/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_38,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_33,negated_conjecture,
% 3.90/0.98      ( v1_funct_2(sK6,sK4,sK3) ),
% 3.90/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_30,negated_conjecture,
% 3.90/0.98      ( v1_funct_2(sK7,sK5,sK3) ),
% 3.90/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_973,plain,
% 3.90/0.98      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 3.90/0.98      theory(equality) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2090,plain,
% 3.90/0.98      ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != X0_57
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != X0_57
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_973]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2274,plain,
% 3.90/0.98      ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2090]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_969,plain,( X0_57 = X0_57 ),theory(equality) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2275,plain,
% 3.90/0.98      ( k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_969]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2544,plain,
% 3.90/0.98      ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != X0_57
% 3.90/0.98      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != X0_57 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_973]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3510,plain,
% 3.90/0.98      ( k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5))
% 3.90/0.98      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5))
% 3.90/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2544]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3511,plain,
% 3.90/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) = k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2347]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_24,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X3)
% 3.90/0.98      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X1)
% 3.90/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.90/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_27,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X3)
% 3.90/0.98      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_26,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X3)
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_25,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X3)
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_222,plain,
% 3.90/0.98      ( ~ v1_funct_1(X3)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X1)
% 3.90/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_24,c_27,c_26,c_25]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_223,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X3)
% 3.90/0.98      | v1_xboole_0(X1)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_222]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_935,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 3.90/0.98      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 3.90/0.98      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 3.90/0.98      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 3.90/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 3.90/0.98      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 3.90/0.98      | ~ v1_funct_1(X0_57)
% 3.90/0.98      | ~ v1_funct_1(X3_57)
% 3.90/0.98      | v1_xboole_0(X2_57)
% 3.90/0.98      | v1_xboole_0(X1_57)
% 3.90/0.98      | v1_xboole_0(X4_57)
% 3.90/0.98      | v1_xboole_0(X5_57)
% 3.90/0.98      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_223]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2231,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 3.90/0.98      | ~ v1_funct_2(sK6,X3_57,X2_57)
% 3.90/0.98      | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
% 3.90/0.98      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
% 3.90/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
% 3.90/0.98      | ~ v1_funct_1(X0_57)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(X2_57)
% 3.90/0.98      | v1_xboole_0(X1_57)
% 3.90/0.98      | v1_xboole_0(X4_57)
% 3.90/0.98      | v1_xboole_0(X3_57)
% 3.90/0.98      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X4_57,X3_57,X1_57)) != k2_partfun1(X3_57,X2_57,sK6,k9_subset_1(X4_57,X3_57,X1_57))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X4_57,X3_57,X1_57),X2_57,k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK6,X0_57),X3_57) = sK6 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_935]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2461,plain,
% 3.90/0.98      ( ~ v1_funct_2(sK7,X0_57,X1_57)
% 3.90/0.98      | ~ v1_funct_2(sK6,X2_57,X1_57)
% 3.90/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
% 3.90/0.98      | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
% 3.90/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(X2_57)
% 3.90/0.98      | v1_xboole_0(X1_57)
% 3.90/0.98      | v1_xboole_0(X3_57)
% 3.90/0.98      | v1_xboole_0(X0_57)
% 3.90/0.98      | k2_partfun1(X0_57,X1_57,sK7,k9_subset_1(X3_57,X2_57,X0_57)) != k2_partfun1(X2_57,X1_57,sK6,k9_subset_1(X3_57,X2_57,X0_57))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X3_57,X2_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK6,sK7),X2_57) = sK6 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2231]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2941,plain,
% 3.90/0.98      ( ~ v1_funct_2(sK7,X0_57,sK3)
% 3.90/0.98      | ~ v1_funct_2(sK6,sK4,sK3)
% 3.90/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 3.90/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(X1_57))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(X1_57)
% 3.90/0.98      | v1_xboole_0(X0_57)
% 3.90/0.98      | v1_xboole_0(sK3)
% 3.90/0.98      | v1_xboole_0(sK4)
% 3.90/0.98      | k2_partfun1(X0_57,sK3,sK7,k9_subset_1(X1_57,sK4,X0_57)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X1_57,sK4,X0_57))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X1_57,sK4,X0_57),sK3,k1_tmap_1(X1_57,sK3,sK4,X0_57,sK6,sK7),sK4) = sK6 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2461]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3362,plain,
% 3.90/0.98      ( ~ v1_funct_2(sK7,sK5,sK3)
% 3.90/0.98      | ~ v1_funct_2(sK6,sK4,sK3)
% 3.90/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(X0_57))
% 3.90/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0_57))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(X0_57)
% 3.90/0.98      | v1_xboole_0(sK3)
% 3.90/0.98      | v1_xboole_0(sK5)
% 3.90/0.98      | v1_xboole_0(sK4)
% 3.90/0.98      | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.90/0.98      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(X0_57,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X0_57,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2941]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4587,plain,
% 3.90/0.98      ( ~ v1_funct_2(sK7,sK5,sK3)
% 3.90/0.98      | ~ v1_funct_2(sK6,sK4,sK3)
% 3.90/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 3.90/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(sK3)
% 3.90/0.98      | v1_xboole_0(sK5)
% 3.90/0.98      | v1_xboole_0(sK4)
% 3.90/0.98      | v1_xboole_0(sK2)
% 3.90/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.90/0.98      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_3362]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_23,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X3)
% 3.90/0.98      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X1)
% 3.90/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_229,plain,
% 3.90/0.98      ( ~ v1_funct_1(X3)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X1)
% 3.90/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_23,c_27,c_26,c_25]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_230,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.90/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X3)
% 3.90/0.98      | v1_xboole_0(X1)
% 3.90/0.98      | v1_xboole_0(X2)
% 3.90/0.98      | v1_xboole_0(X4)
% 3.90/0.98      | v1_xboole_0(X5)
% 3.90/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_229]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_934,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 3.90/0.98      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 3.90/0.98      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 3.90/0.98      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 3.90/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 3.90/0.98      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 3.90/0.98      | ~ v1_funct_1(X0_57)
% 3.90/0.98      | ~ v1_funct_1(X3_57)
% 3.90/0.98      | v1_xboole_0(X2_57)
% 3.90/0.98      | v1_xboole_0(X1_57)
% 3.90/0.98      | v1_xboole_0(X4_57)
% 3.90/0.98      | v1_xboole_0(X5_57)
% 3.90/0.98      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
% 3.90/0.98      inference(subtyping,[status(esa)],[c_230]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2221,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 3.90/0.98      | ~ v1_funct_2(sK6,X3_57,X2_57)
% 3.90/0.98      | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
% 3.90/0.98      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
% 3.90/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
% 3.90/0.98      | ~ v1_funct_1(X0_57)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(X2_57)
% 3.90/0.98      | v1_xboole_0(X1_57)
% 3.90/0.98      | v1_xboole_0(X4_57)
% 3.90/0.98      | v1_xboole_0(X3_57)
% 3.90/0.98      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X4_57,X3_57,X1_57)) != k2_partfun1(X3_57,X2_57,sK6,k9_subset_1(X4_57,X3_57,X1_57))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X4_57,X3_57,X1_57),X2_57,k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK6,X0_57),X1_57) = X0_57 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_934]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2521,plain,
% 3.90/0.98      ( ~ v1_funct_2(sK7,X0_57,X1_57)
% 3.90/0.98      | ~ v1_funct_2(sK6,X2_57,X1_57)
% 3.90/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
% 3.90/0.98      | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
% 3.90/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(X2_57)
% 3.90/0.98      | v1_xboole_0(X1_57)
% 3.90/0.98      | v1_xboole_0(X3_57)
% 3.90/0.98      | v1_xboole_0(X0_57)
% 3.90/0.98      | k2_partfun1(X0_57,X1_57,sK7,k9_subset_1(X3_57,X2_57,X0_57)) != k2_partfun1(X2_57,X1_57,sK6,k9_subset_1(X3_57,X2_57,X0_57))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X3_57,X2_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK6,sK7),X0_57) = sK7 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2221]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2969,plain,
% 3.90/0.98      ( ~ v1_funct_2(sK7,X0_57,sK3)
% 3.90/0.98      | ~ v1_funct_2(sK6,sK4,sK3)
% 3.90/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 3.90/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(X1_57))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(X1_57)
% 3.90/0.98      | v1_xboole_0(X0_57)
% 3.90/0.98      | v1_xboole_0(sK3)
% 3.90/0.98      | v1_xboole_0(sK4)
% 3.90/0.98      | k2_partfun1(X0_57,sK3,sK7,k9_subset_1(X1_57,sK4,X0_57)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X1_57,sK4,X0_57))
% 3.90/0.98      | k2_partfun1(k4_subset_1(X1_57,sK4,X0_57),sK3,k1_tmap_1(X1_57,sK3,sK4,X0_57,sK6,sK7),X0_57) = sK7 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2521]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3383,plain,
% 3.90/0.98      ( ~ v1_funct_2(sK7,sK5,sK3)
% 3.90/0.98      | ~ v1_funct_2(sK6,sK4,sK3)
% 3.90/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(X0_57))
% 3.90/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0_57))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(X0_57)
% 3.90/0.98      | v1_xboole_0(sK3)
% 3.90/0.98      | v1_xboole_0(sK5)
% 3.90/0.98      | v1_xboole_0(sK4)
% 3.90/0.98      | k2_partfun1(k4_subset_1(X0_57,sK4,sK5),sK3,k1_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.90/0.98      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(X0_57,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(X0_57,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_2969]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4599,plain,
% 3.90/0.98      ( ~ v1_funct_2(sK7,sK5,sK3)
% 3.90/0.98      | ~ v1_funct_2(sK6,sK4,sK3)
% 3.90/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.90/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 3.90/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 3.90/0.98      | ~ v1_funct_1(sK7)
% 3.90/0.98      | ~ v1_funct_1(sK6)
% 3.90/0.98      | v1_xboole_0(sK3)
% 3.90/0.98      | v1_xboole_0(sK5)
% 3.90/0.98      | v1_xboole_0(sK4)
% 3.90/0.98      | v1_xboole_0(sK2)
% 3.90/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.90/0.98      | k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_3383]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4867,plain,
% 3.90/0.98      ( k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_4849,c_41,c_40,c_39,c_38,c_37,c_36,c_34,c_33,c_32,
% 3.90/0.98                 c_31,c_30,c_29,c_948,c_2274,c_2275,c_3510,c_3511,c_4587,
% 3.90/0.98                 c_4599]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5575,plain,
% 3.90/0.98      ( k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_5572,c_4867]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8700,plain,
% 3.90/0.98      ( k7_relat_1(sK7,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2473,c_5575]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8915,plain,
% 3.90/0.98      ( k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4137,c_8700]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8916,plain,
% 3.90/0.98      ( k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK4,sK5))) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2473,c_8915]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_9152,plain,
% 3.90/0.98      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4137,c_8916]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_9297,plain,
% 3.90/0.98      ( k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_5738,c_9152]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2869,plain,
% 3.90/0.98      ( v1_relat_1(k2_zfmisc_1(sK4,sK3)) != iProver_top
% 3.90/0.98      | v1_relat_1(sK6) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1911,c_1900]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2487,plain,
% 3.90/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK3)) | v1_relat_1(sK6) ),
% 3.90/0.98      inference(resolution,[status(thm)],[c_956,c_944]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2566,plain,
% 3.90/0.98      ( v1_relat_1(sK6) ),
% 3.90/0.98      inference(forward_subsumption_resolution,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_2487,c_955]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2567,plain,
% 3.90/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_2566]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4646,plain,
% 3.90/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_2869,c_2567]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5739,plain,
% 3.90/0.98      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4646,c_5090]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(contradiction,plain,
% 3.90/0.98      ( $false ),
% 3.90/0.98      inference(minisat,[status(thm)],[c_9297,c_5739]) ).
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  ------                               Statistics
% 3.90/0.98  
% 3.90/0.98  ------ Selected
% 3.90/0.98  
% 3.90/0.98  total_time:                             0.476
% 3.90/0.98  
%------------------------------------------------------------------------------
