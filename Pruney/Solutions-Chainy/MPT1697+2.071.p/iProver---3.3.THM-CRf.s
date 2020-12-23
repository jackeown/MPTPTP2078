%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:38 EST 2020

% Result     : Theorem 7.00s
% Output     : CNFRefutation 7.00s
% Verified   : 
% Statistics : Number of formulae       :  239 (3108 expanded)
%              Number of clauses        :  163 ( 847 expanded)
%              Number of leaves         :   20 (1176 expanded)
%              Depth                    :   29
%              Number of atoms          : 1315 (38528 expanded)
%              Number of equality atoms :  559 (9191 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f44,f43,f42,f41,f40,f39])).

fof(f78,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
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

fof(f14,plain,(
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

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
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
    inference(equality_resolution,[],[f60])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
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
    inference(equality_resolution,[],[f61])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1099,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1917,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1106,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1911,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_3256,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1911])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1112,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1905,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1112])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1109,plain,
    ( r1_xboole_0(X0_54,X1_54)
    | r2_hidden(sK1(X0_54,X1_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1908,plain,
    ( r1_xboole_0(X0_54,X1_54) = iProver_top
    | r2_hidden(sK1(X0_54,X1_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1115,plain,
    ( ~ r2_hidden(X0_56,X0_54)
    | ~ v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1902,plain,
    ( r2_hidden(X0_56,X0_54) != iProver_top
    | v1_xboole_0(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1115])).

cnf(c_3251,plain,
    ( r1_xboole_0(X0_54,X1_54) = iProver_top
    | v1_xboole_0(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1902])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1113,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | k3_xboole_0(X0_54,X1_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1904,plain,
    ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(X0_54,X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_5110,plain,
    ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
    | v1_xboole_0(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_1904])).

cnf(c_6105,plain,
    ( k3_xboole_0(k1_xboole_0,X0_54) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1905,c_5110])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1114,plain,
    ( r1_xboole_0(X0_54,X1_54)
    | k3_xboole_0(X0_54,X1_54) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1903,plain,
    ( k3_xboole_0(X0_54,X1_54) != k1_xboole_0
    | r1_xboole_0(X0_54,X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_6139,plain,
    ( r1_xboole_0(k1_xboole_0,X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_6105,c_1903])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1107,plain,
    ( ~ r1_xboole_0(X0_54,k1_relat_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | k7_relat_1(X1_54,X0_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1910,plain,
    ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(X1_54,k1_relat_1(X0_54)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1107])).

cnf(c_6153,plain,
    ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_6139,c_1910])).

cnf(c_7310,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3256,c_6153])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1105,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1912,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1105])).

cnf(c_3519,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1912])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2348,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0_54,X1_54,sK7,X2_54) = k7_relat_1(sK7,X2_54) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_2537,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54) ),
    inference(instantiation,[status(thm)],[c_2348])).

cnf(c_3942,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3519,c_23,c_21,c_2537])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1093,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1923,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1909,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_3179,plain,
    ( k9_subset_1(sK2,X0_54,sK5) = k3_xboole_0(X0_54,sK5) ),
    inference(superposition,[status(thm)],[c_1923,c_1909])).

cnf(c_20,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1100,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3353,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_3179,c_1100])).

cnf(c_11,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_458,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_459,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_461,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_31,c_29])).

cnf(c_1085,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_461])).

cnf(c_1931,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_2820,plain,
    ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1931,c_1904])).

cnf(c_3354,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3353,c_2820])).

cnf(c_3946,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3942,c_3354])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1096,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1920,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_3520,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_1912])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2353,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0_54,X1_54,sK6,X2_54) = k7_relat_1(sK6,X2_54) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_2542,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54) ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_3948,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3520,c_26,c_24,c_2542])).

cnf(c_4038,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3946,c_3948])).

cnf(c_7749,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7310,c_4038])).

cnf(c_2269,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_2467,plain,
    ( r1_xboole_0(k1_xboole_0,X0_54)
    | r2_hidden(sK1(k1_xboole_0,X0_54),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_2796,plain,
    ( r1_xboole_0(k1_xboole_0,k1_relat_1(sK6))
    | r2_hidden(sK1(k1_xboole_0,k1_relat_1(sK6)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_2455,plain,
    ( ~ r1_xboole_0(X0_54,k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k7_relat_1(sK6,X0_54) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_2797,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2455])).

cnf(c_2257,plain,
    ( ~ r2_hidden(X0_56,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_2466,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,X0_54),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_3697,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k1_relat_1(sK6)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2466])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_182,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_19,c_18,c_17])).

cnf(c_183,plain,
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
    inference(renaming,[status(thm)],[c_182])).

cnf(c_1087,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_183])).

cnf(c_1929,plain,
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
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_5697,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3942,c_1929])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_38,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_44,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_45,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6186,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
    | k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5697,c_35,c_38,c_44,c_45,c_46])).

cnf(c_6187,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6186])).

cnf(c_6202,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3948,c_6187])).

cnf(c_36,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_42,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_43,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6303,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6202,c_36,c_41,c_42,c_43])).

cnf(c_6304,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6303])).

cnf(c_6314,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3179,c_6304])).

cnf(c_6315,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6314,c_2820])).

cnf(c_6316,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6315,c_3179])).

cnf(c_6317,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6316,c_2820])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6318,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6317])).

cnf(c_17308,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6317,c_33,c_30,c_28,c_6318])).

cnf(c_17309,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_17308])).

cnf(c_3257,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_1911])).

cnf(c_7311,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3257,c_6153])).

cnf(c_17310,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17309,c_7310,c_7311])).

cnf(c_17311,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_17310])).

cnf(c_19186,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7749,c_24,c_4,c_2269,c_2796,c_2797,c_3697,c_17311])).

cnf(c_1103,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1914,plain,
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
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_3729,plain,
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
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_1912])).

cnf(c_1101,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1916,plain,
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
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_11873,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3729,c_1916])).

cnf(c_11877,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
    | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_11873])).

cnf(c_11984,plain,
    ( v1_funct_1(X2_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
    | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11877,c_35,c_38,c_44,c_45])).

cnf(c_11985,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
    | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_11984])).

cnf(c_11999,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_11985])).

cnf(c_12454,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11999,c_36,c_41,c_42])).

cnf(c_12455,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_12454])).

cnf(c_12464,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54)
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_12455])).

cnf(c_34,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12469,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12464,c_34,c_37])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_189,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_19,c_18,c_17])).

cnf(c_190,plain,
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
    inference(renaming,[status(thm)],[c_189])).

cnf(c_1086,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_190])).

cnf(c_1930,plain,
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
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_6984,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3942,c_1930])).

cnf(c_14525,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6984,c_35,c_38,c_44,c_45,c_46])).

cnf(c_14526,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_14525])).

cnf(c_14546,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,X0_54,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3179,c_14526])).

cnf(c_14556,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14546,c_3179])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14718,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14556,c_34,c_39])).

cnf(c_14719,plain,
    ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
    | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
    | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_14718])).

cnf(c_14732,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3948,c_14719])).

cnf(c_14817,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14732,c_2820,c_7310,c_7311])).

cnf(c_14818,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14817])).

cnf(c_14819,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14818,c_12469])).

cnf(c_14541,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3948,c_14526])).

cnf(c_14700,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14541,c_36,c_41,c_42,c_43])).

cnf(c_14701,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_14700])).

cnf(c_14711,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3179,c_14701])).

cnf(c_14712,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14711,c_2820,c_7310])).

cnf(c_14713,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14712,c_3179,c_12469])).

cnf(c_14714,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14713,c_2820,c_7311])).

cnf(c_14715,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14714])).

cnf(c_15058,plain,
    ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14819,c_34,c_37,c_39,c_14715])).

cnf(c_19188,plain,
    ( sK7 != sK7 ),
    inference(demodulation,[status(thm)],[c_19186,c_12469,c_15058])).

cnf(c_19189,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19188])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.00/1.58  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/1.58  
% 7.00/1.58  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.00/1.58  
% 7.00/1.58  ------  iProver source info
% 7.00/1.58  
% 7.00/1.58  git: date: 2020-06-30 10:37:57 +0100
% 7.00/1.58  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.00/1.58  git: non_committed_changes: false
% 7.00/1.58  git: last_make_outside_of_git: false
% 7.00/1.58  
% 7.00/1.58  ------ 
% 7.00/1.58  
% 7.00/1.58  ------ Input Options
% 7.00/1.58  
% 7.00/1.58  --out_options                           all
% 7.00/1.58  --tptp_safe_out                         true
% 7.00/1.58  --problem_path                          ""
% 7.00/1.58  --include_path                          ""
% 7.00/1.58  --clausifier                            res/vclausify_rel
% 7.00/1.58  --clausifier_options                    --mode clausify
% 7.00/1.58  --stdin                                 false
% 7.00/1.58  --stats_out                             all
% 7.00/1.58  
% 7.00/1.58  ------ General Options
% 7.00/1.58  
% 7.00/1.58  --fof                                   false
% 7.00/1.58  --time_out_real                         305.
% 7.00/1.58  --time_out_virtual                      -1.
% 7.00/1.58  --symbol_type_check                     false
% 7.00/1.58  --clausify_out                          false
% 7.00/1.58  --sig_cnt_out                           false
% 7.00/1.58  --trig_cnt_out                          false
% 7.00/1.58  --trig_cnt_out_tolerance                1.
% 7.00/1.58  --trig_cnt_out_sk_spl                   false
% 7.00/1.58  --abstr_cl_out                          false
% 7.00/1.58  
% 7.00/1.58  ------ Global Options
% 7.00/1.58  
% 7.00/1.58  --schedule                              default
% 7.00/1.58  --add_important_lit                     false
% 7.00/1.58  --prop_solver_per_cl                    1000
% 7.00/1.58  --min_unsat_core                        false
% 7.00/1.58  --soft_assumptions                      false
% 7.00/1.58  --soft_lemma_size                       3
% 7.00/1.58  --prop_impl_unit_size                   0
% 7.00/1.58  --prop_impl_unit                        []
% 7.00/1.58  --share_sel_clauses                     true
% 7.00/1.58  --reset_solvers                         false
% 7.00/1.58  --bc_imp_inh                            [conj_cone]
% 7.00/1.58  --conj_cone_tolerance                   3.
% 7.00/1.58  --extra_neg_conj                        none
% 7.00/1.58  --large_theory_mode                     true
% 7.00/1.58  --prolific_symb_bound                   200
% 7.00/1.58  --lt_threshold                          2000
% 7.00/1.58  --clause_weak_htbl                      true
% 7.00/1.58  --gc_record_bc_elim                     false
% 7.00/1.58  
% 7.00/1.58  ------ Preprocessing Options
% 7.00/1.58  
% 7.00/1.58  --preprocessing_flag                    true
% 7.00/1.58  --time_out_prep_mult                    0.1
% 7.00/1.58  --splitting_mode                        input
% 7.00/1.58  --splitting_grd                         true
% 7.00/1.58  --splitting_cvd                         false
% 7.00/1.58  --splitting_cvd_svl                     false
% 7.00/1.58  --splitting_nvd                         32
% 7.00/1.58  --sub_typing                            true
% 7.00/1.58  --prep_gs_sim                           true
% 7.00/1.58  --prep_unflatten                        true
% 7.00/1.58  --prep_res_sim                          true
% 7.00/1.58  --prep_upred                            true
% 7.00/1.58  --prep_sem_filter                       exhaustive
% 7.00/1.58  --prep_sem_filter_out                   false
% 7.00/1.58  --pred_elim                             true
% 7.00/1.58  --res_sim_input                         true
% 7.00/1.58  --eq_ax_congr_red                       true
% 7.00/1.58  --pure_diseq_elim                       true
% 7.00/1.58  --brand_transform                       false
% 7.00/1.58  --non_eq_to_eq                          false
% 7.00/1.58  --prep_def_merge                        true
% 7.00/1.58  --prep_def_merge_prop_impl              false
% 7.00/1.58  --prep_def_merge_mbd                    true
% 7.00/1.58  --prep_def_merge_tr_red                 false
% 7.00/1.58  --prep_def_merge_tr_cl                  false
% 7.00/1.58  --smt_preprocessing                     true
% 7.00/1.58  --smt_ac_axioms                         fast
% 7.00/1.58  --preprocessed_out                      false
% 7.00/1.58  --preprocessed_stats                    false
% 7.00/1.58  
% 7.00/1.58  ------ Abstraction refinement Options
% 7.00/1.58  
% 7.00/1.58  --abstr_ref                             []
% 7.00/1.58  --abstr_ref_prep                        false
% 7.00/1.58  --abstr_ref_until_sat                   false
% 7.00/1.58  --abstr_ref_sig_restrict                funpre
% 7.00/1.58  --abstr_ref_af_restrict_to_split_sk     false
% 7.00/1.58  --abstr_ref_under                       []
% 7.00/1.58  
% 7.00/1.58  ------ SAT Options
% 7.00/1.58  
% 7.00/1.58  --sat_mode                              false
% 7.00/1.58  --sat_fm_restart_options                ""
% 7.00/1.58  --sat_gr_def                            false
% 7.00/1.58  --sat_epr_types                         true
% 7.00/1.58  --sat_non_cyclic_types                  false
% 7.00/1.58  --sat_finite_models                     false
% 7.00/1.58  --sat_fm_lemmas                         false
% 7.00/1.58  --sat_fm_prep                           false
% 7.00/1.58  --sat_fm_uc_incr                        true
% 7.00/1.58  --sat_out_model                         small
% 7.00/1.58  --sat_out_clauses                       false
% 7.00/1.58  
% 7.00/1.58  ------ QBF Options
% 7.00/1.58  
% 7.00/1.58  --qbf_mode                              false
% 7.00/1.58  --qbf_elim_univ                         false
% 7.00/1.58  --qbf_dom_inst                          none
% 7.00/1.58  --qbf_dom_pre_inst                      false
% 7.00/1.58  --qbf_sk_in                             false
% 7.00/1.58  --qbf_pred_elim                         true
% 7.00/1.58  --qbf_split                             512
% 7.00/1.58  
% 7.00/1.58  ------ BMC1 Options
% 7.00/1.58  
% 7.00/1.58  --bmc1_incremental                      false
% 7.00/1.58  --bmc1_axioms                           reachable_all
% 7.00/1.58  --bmc1_min_bound                        0
% 7.00/1.58  --bmc1_max_bound                        -1
% 7.00/1.58  --bmc1_max_bound_default                -1
% 7.00/1.58  --bmc1_symbol_reachability              true
% 7.00/1.58  --bmc1_property_lemmas                  false
% 7.00/1.58  --bmc1_k_induction                      false
% 7.00/1.58  --bmc1_non_equiv_states                 false
% 7.00/1.58  --bmc1_deadlock                         false
% 7.00/1.58  --bmc1_ucm                              false
% 7.00/1.58  --bmc1_add_unsat_core                   none
% 7.00/1.58  --bmc1_unsat_core_children              false
% 7.00/1.58  --bmc1_unsat_core_extrapolate_axioms    false
% 7.00/1.58  --bmc1_out_stat                         full
% 7.00/1.58  --bmc1_ground_init                      false
% 7.00/1.58  --bmc1_pre_inst_next_state              false
% 7.00/1.58  --bmc1_pre_inst_state                   false
% 7.00/1.58  --bmc1_pre_inst_reach_state             false
% 7.00/1.58  --bmc1_out_unsat_core                   false
% 7.00/1.58  --bmc1_aig_witness_out                  false
% 7.00/1.58  --bmc1_verbose                          false
% 7.00/1.58  --bmc1_dump_clauses_tptp                false
% 7.00/1.58  --bmc1_dump_unsat_core_tptp             false
% 7.00/1.58  --bmc1_dump_file                        -
% 7.00/1.58  --bmc1_ucm_expand_uc_limit              128
% 7.00/1.58  --bmc1_ucm_n_expand_iterations          6
% 7.00/1.58  --bmc1_ucm_extend_mode                  1
% 7.00/1.58  --bmc1_ucm_init_mode                    2
% 7.00/1.58  --bmc1_ucm_cone_mode                    none
% 7.00/1.58  --bmc1_ucm_reduced_relation_type        0
% 7.00/1.58  --bmc1_ucm_relax_model                  4
% 7.00/1.58  --bmc1_ucm_full_tr_after_sat            true
% 7.00/1.58  --bmc1_ucm_expand_neg_assumptions       false
% 7.00/1.58  --bmc1_ucm_layered_model                none
% 7.00/1.58  --bmc1_ucm_max_lemma_size               10
% 7.00/1.58  
% 7.00/1.58  ------ AIG Options
% 7.00/1.58  
% 7.00/1.58  --aig_mode                              false
% 7.00/1.58  
% 7.00/1.58  ------ Instantiation Options
% 7.00/1.58  
% 7.00/1.58  --instantiation_flag                    true
% 7.00/1.58  --inst_sos_flag                         false
% 7.00/1.58  --inst_sos_phase                        true
% 7.00/1.58  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.00/1.58  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.00/1.58  --inst_lit_sel_side                     num_symb
% 7.00/1.58  --inst_solver_per_active                1400
% 7.00/1.58  --inst_solver_calls_frac                1.
% 7.00/1.58  --inst_passive_queue_type               priority_queues
% 7.00/1.58  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.00/1.58  --inst_passive_queues_freq              [25;2]
% 7.00/1.58  --inst_dismatching                      true
% 7.00/1.58  --inst_eager_unprocessed_to_passive     true
% 7.00/1.58  --inst_prop_sim_given                   true
% 7.00/1.58  --inst_prop_sim_new                     false
% 7.00/1.58  --inst_subs_new                         false
% 7.00/1.58  --inst_eq_res_simp                      false
% 7.00/1.58  --inst_subs_given                       false
% 7.00/1.58  --inst_orphan_elimination               true
% 7.00/1.58  --inst_learning_loop_flag               true
% 7.00/1.58  --inst_learning_start                   3000
% 7.00/1.58  --inst_learning_factor                  2
% 7.00/1.58  --inst_start_prop_sim_after_learn       3
% 7.00/1.58  --inst_sel_renew                        solver
% 7.00/1.58  --inst_lit_activity_flag                true
% 7.00/1.58  --inst_restr_to_given                   false
% 7.00/1.58  --inst_activity_threshold               500
% 7.00/1.58  --inst_out_proof                        true
% 7.00/1.58  
% 7.00/1.58  ------ Resolution Options
% 7.00/1.58  
% 7.00/1.58  --resolution_flag                       true
% 7.00/1.58  --res_lit_sel                           adaptive
% 7.00/1.58  --res_lit_sel_side                      none
% 7.00/1.58  --res_ordering                          kbo
% 7.00/1.58  --res_to_prop_solver                    active
% 7.00/1.58  --res_prop_simpl_new                    false
% 7.00/1.58  --res_prop_simpl_given                  true
% 7.00/1.58  --res_passive_queue_type                priority_queues
% 7.00/1.58  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.00/1.58  --res_passive_queues_freq               [15;5]
% 7.00/1.58  --res_forward_subs                      full
% 7.00/1.58  --res_backward_subs                     full
% 7.00/1.58  --res_forward_subs_resolution           true
% 7.00/1.58  --res_backward_subs_resolution          true
% 7.00/1.58  --res_orphan_elimination                true
% 7.00/1.58  --res_time_limit                        2.
% 7.00/1.58  --res_out_proof                         true
% 7.00/1.58  
% 7.00/1.58  ------ Superposition Options
% 7.00/1.58  
% 7.00/1.58  --superposition_flag                    true
% 7.00/1.58  --sup_passive_queue_type                priority_queues
% 7.00/1.58  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.00/1.58  --sup_passive_queues_freq               [8;1;4]
% 7.00/1.58  --demod_completeness_check              fast
% 7.00/1.58  --demod_use_ground                      true
% 7.00/1.58  --sup_to_prop_solver                    passive
% 7.00/1.58  --sup_prop_simpl_new                    true
% 7.00/1.58  --sup_prop_simpl_given                  true
% 7.00/1.58  --sup_fun_splitting                     false
% 7.00/1.58  --sup_smt_interval                      50000
% 7.00/1.58  
% 7.00/1.58  ------ Superposition Simplification Setup
% 7.00/1.58  
% 7.00/1.58  --sup_indices_passive                   []
% 7.00/1.58  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.00/1.58  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.00/1.58  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.00/1.58  --sup_full_triv                         [TrivRules;PropSubs]
% 7.00/1.58  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.00/1.58  --sup_full_bw                           [BwDemod]
% 7.00/1.58  --sup_immed_triv                        [TrivRules]
% 7.00/1.58  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.00/1.58  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.00/1.58  --sup_immed_bw_main                     []
% 7.00/1.58  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.00/1.58  --sup_input_triv                        [Unflattening;TrivRules]
% 7.00/1.58  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.00/1.58  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.00/1.58  
% 7.00/1.58  ------ Combination Options
% 7.00/1.58  
% 7.00/1.58  --comb_res_mult                         3
% 7.00/1.58  --comb_sup_mult                         2
% 7.00/1.58  --comb_inst_mult                        10
% 7.00/1.58  
% 7.00/1.58  ------ Debug Options
% 7.00/1.58  
% 7.00/1.58  --dbg_backtrace                         false
% 7.00/1.58  --dbg_dump_prop_clauses                 false
% 7.00/1.58  --dbg_dump_prop_clauses_file            -
% 7.00/1.58  --dbg_out_stat                          false
% 7.00/1.58  ------ Parsing...
% 7.00/1.58  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.00/1.58  
% 7.00/1.58  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.00/1.58  
% 7.00/1.58  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.00/1.58  
% 7.00/1.58  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.00/1.58  ------ Proving...
% 7.00/1.58  ------ Problem Properties 
% 7.00/1.58  
% 7.00/1.58  
% 7.00/1.58  clauses                                 32
% 7.00/1.58  conjectures                             13
% 7.00/1.58  EPR                                     12
% 7.00/1.58  Horn                                    23
% 7.00/1.58  unary                                   14
% 7.00/1.58  binary                                  8
% 7.00/1.58  lits                                    126
% 7.00/1.58  lits eq                                 14
% 7.00/1.58  fd_pure                                 0
% 7.00/1.58  fd_pseudo                               0
% 7.00/1.58  fd_cond                                 0
% 7.00/1.58  fd_pseudo_cond                          0
% 7.00/1.58  AC symbols                              0
% 7.00/1.58  
% 7.00/1.58  ------ Schedule dynamic 5 is on 
% 7.00/1.58  
% 7.00/1.58  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.00/1.58  
% 7.00/1.58  
% 7.00/1.58  ------ 
% 7.00/1.58  Current options:
% 7.00/1.58  ------ 
% 7.00/1.58  
% 7.00/1.58  ------ Input Options
% 7.00/1.58  
% 7.00/1.58  --out_options                           all
% 7.00/1.58  --tptp_safe_out                         true
% 7.00/1.58  --problem_path                          ""
% 7.00/1.58  --include_path                          ""
% 7.00/1.58  --clausifier                            res/vclausify_rel
% 7.00/1.58  --clausifier_options                    --mode clausify
% 7.00/1.58  --stdin                                 false
% 7.00/1.58  --stats_out                             all
% 7.00/1.58  
% 7.00/1.58  ------ General Options
% 7.00/1.58  
% 7.00/1.58  --fof                                   false
% 7.00/1.58  --time_out_real                         305.
% 7.00/1.58  --time_out_virtual                      -1.
% 7.00/1.58  --symbol_type_check                     false
% 7.00/1.58  --clausify_out                          false
% 7.00/1.58  --sig_cnt_out                           false
% 7.00/1.58  --trig_cnt_out                          false
% 7.00/1.58  --trig_cnt_out_tolerance                1.
% 7.00/1.58  --trig_cnt_out_sk_spl                   false
% 7.00/1.58  --abstr_cl_out                          false
% 7.00/1.58  
% 7.00/1.58  ------ Global Options
% 7.00/1.58  
% 7.00/1.58  --schedule                              default
% 7.00/1.58  --add_important_lit                     false
% 7.00/1.58  --prop_solver_per_cl                    1000
% 7.00/1.58  --min_unsat_core                        false
% 7.00/1.58  --soft_assumptions                      false
% 7.00/1.58  --soft_lemma_size                       3
% 7.00/1.58  --prop_impl_unit_size                   0
% 7.00/1.58  --prop_impl_unit                        []
% 7.00/1.58  --share_sel_clauses                     true
% 7.00/1.58  --reset_solvers                         false
% 7.00/1.58  --bc_imp_inh                            [conj_cone]
% 7.00/1.58  --conj_cone_tolerance                   3.
% 7.00/1.58  --extra_neg_conj                        none
% 7.00/1.58  --large_theory_mode                     true
% 7.00/1.58  --prolific_symb_bound                   200
% 7.00/1.58  --lt_threshold                          2000
% 7.00/1.58  --clause_weak_htbl                      true
% 7.00/1.58  --gc_record_bc_elim                     false
% 7.00/1.58  
% 7.00/1.58  ------ Preprocessing Options
% 7.00/1.58  
% 7.00/1.58  --preprocessing_flag                    true
% 7.00/1.58  --time_out_prep_mult                    0.1
% 7.00/1.58  --splitting_mode                        input
% 7.00/1.58  --splitting_grd                         true
% 7.00/1.58  --splitting_cvd                         false
% 7.00/1.58  --splitting_cvd_svl                     false
% 7.00/1.58  --splitting_nvd                         32
% 7.00/1.58  --sub_typing                            true
% 7.00/1.58  --prep_gs_sim                           true
% 7.00/1.58  --prep_unflatten                        true
% 7.00/1.58  --prep_res_sim                          true
% 7.00/1.58  --prep_upred                            true
% 7.00/1.58  --prep_sem_filter                       exhaustive
% 7.00/1.58  --prep_sem_filter_out                   false
% 7.00/1.58  --pred_elim                             true
% 7.00/1.58  --res_sim_input                         true
% 7.00/1.58  --eq_ax_congr_red                       true
% 7.00/1.58  --pure_diseq_elim                       true
% 7.00/1.58  --brand_transform                       false
% 7.00/1.58  --non_eq_to_eq                          false
% 7.00/1.58  --prep_def_merge                        true
% 7.00/1.58  --prep_def_merge_prop_impl              false
% 7.00/1.58  --prep_def_merge_mbd                    true
% 7.00/1.58  --prep_def_merge_tr_red                 false
% 7.00/1.58  --prep_def_merge_tr_cl                  false
% 7.00/1.58  --smt_preprocessing                     true
% 7.00/1.58  --smt_ac_axioms                         fast
% 7.00/1.58  --preprocessed_out                      false
% 7.00/1.58  --preprocessed_stats                    false
% 7.00/1.58  
% 7.00/1.58  ------ Abstraction refinement Options
% 7.00/1.58  
% 7.00/1.58  --abstr_ref                             []
% 7.00/1.58  --abstr_ref_prep                        false
% 7.00/1.58  --abstr_ref_until_sat                   false
% 7.00/1.58  --abstr_ref_sig_restrict                funpre
% 7.00/1.58  --abstr_ref_af_restrict_to_split_sk     false
% 7.00/1.58  --abstr_ref_under                       []
% 7.00/1.58  
% 7.00/1.58  ------ SAT Options
% 7.00/1.58  
% 7.00/1.58  --sat_mode                              false
% 7.00/1.58  --sat_fm_restart_options                ""
% 7.00/1.58  --sat_gr_def                            false
% 7.00/1.58  --sat_epr_types                         true
% 7.00/1.58  --sat_non_cyclic_types                  false
% 7.00/1.58  --sat_finite_models                     false
% 7.00/1.58  --sat_fm_lemmas                         false
% 7.00/1.58  --sat_fm_prep                           false
% 7.00/1.58  --sat_fm_uc_incr                        true
% 7.00/1.58  --sat_out_model                         small
% 7.00/1.58  --sat_out_clauses                       false
% 7.00/1.58  
% 7.00/1.58  ------ QBF Options
% 7.00/1.58  
% 7.00/1.58  --qbf_mode                              false
% 7.00/1.58  --qbf_elim_univ                         false
% 7.00/1.58  --qbf_dom_inst                          none
% 7.00/1.58  --qbf_dom_pre_inst                      false
% 7.00/1.58  --qbf_sk_in                             false
% 7.00/1.58  --qbf_pred_elim                         true
% 7.00/1.58  --qbf_split                             512
% 7.00/1.58  
% 7.00/1.58  ------ BMC1 Options
% 7.00/1.58  
% 7.00/1.58  --bmc1_incremental                      false
% 7.00/1.58  --bmc1_axioms                           reachable_all
% 7.00/1.58  --bmc1_min_bound                        0
% 7.00/1.58  --bmc1_max_bound                        -1
% 7.00/1.58  --bmc1_max_bound_default                -1
% 7.00/1.58  --bmc1_symbol_reachability              true
% 7.00/1.58  --bmc1_property_lemmas                  false
% 7.00/1.58  --bmc1_k_induction                      false
% 7.00/1.58  --bmc1_non_equiv_states                 false
% 7.00/1.58  --bmc1_deadlock                         false
% 7.00/1.58  --bmc1_ucm                              false
% 7.00/1.58  --bmc1_add_unsat_core                   none
% 7.00/1.58  --bmc1_unsat_core_children              false
% 7.00/1.58  --bmc1_unsat_core_extrapolate_axioms    false
% 7.00/1.58  --bmc1_out_stat                         full
% 7.00/1.58  --bmc1_ground_init                      false
% 7.00/1.58  --bmc1_pre_inst_next_state              false
% 7.00/1.58  --bmc1_pre_inst_state                   false
% 7.00/1.58  --bmc1_pre_inst_reach_state             false
% 7.00/1.58  --bmc1_out_unsat_core                   false
% 7.00/1.58  --bmc1_aig_witness_out                  false
% 7.00/1.58  --bmc1_verbose                          false
% 7.00/1.58  --bmc1_dump_clauses_tptp                false
% 7.00/1.58  --bmc1_dump_unsat_core_tptp             false
% 7.00/1.58  --bmc1_dump_file                        -
% 7.00/1.58  --bmc1_ucm_expand_uc_limit              128
% 7.00/1.58  --bmc1_ucm_n_expand_iterations          6
% 7.00/1.58  --bmc1_ucm_extend_mode                  1
% 7.00/1.58  --bmc1_ucm_init_mode                    2
% 7.00/1.58  --bmc1_ucm_cone_mode                    none
% 7.00/1.58  --bmc1_ucm_reduced_relation_type        0
% 7.00/1.58  --bmc1_ucm_relax_model                  4
% 7.00/1.58  --bmc1_ucm_full_tr_after_sat            true
% 7.00/1.58  --bmc1_ucm_expand_neg_assumptions       false
% 7.00/1.58  --bmc1_ucm_layered_model                none
% 7.00/1.58  --bmc1_ucm_max_lemma_size               10
% 7.00/1.58  
% 7.00/1.58  ------ AIG Options
% 7.00/1.58  
% 7.00/1.58  --aig_mode                              false
% 7.00/1.58  
% 7.00/1.58  ------ Instantiation Options
% 7.00/1.58  
% 7.00/1.58  --instantiation_flag                    true
% 7.00/1.58  --inst_sos_flag                         false
% 7.00/1.58  --inst_sos_phase                        true
% 7.00/1.58  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.00/1.58  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.00/1.58  --inst_lit_sel_side                     none
% 7.00/1.58  --inst_solver_per_active                1400
% 7.00/1.58  --inst_solver_calls_frac                1.
% 7.00/1.58  --inst_passive_queue_type               priority_queues
% 7.00/1.58  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.00/1.58  --inst_passive_queues_freq              [25;2]
% 7.00/1.58  --inst_dismatching                      true
% 7.00/1.58  --inst_eager_unprocessed_to_passive     true
% 7.00/1.58  --inst_prop_sim_given                   true
% 7.00/1.58  --inst_prop_sim_new                     false
% 7.00/1.58  --inst_subs_new                         false
% 7.00/1.58  --inst_eq_res_simp                      false
% 7.00/1.58  --inst_subs_given                       false
% 7.00/1.58  --inst_orphan_elimination               true
% 7.00/1.58  --inst_learning_loop_flag               true
% 7.00/1.58  --inst_learning_start                   3000
% 7.00/1.58  --inst_learning_factor                  2
% 7.00/1.58  --inst_start_prop_sim_after_learn       3
% 7.00/1.58  --inst_sel_renew                        solver
% 7.00/1.58  --inst_lit_activity_flag                true
% 7.00/1.58  --inst_restr_to_given                   false
% 7.00/1.58  --inst_activity_threshold               500
% 7.00/1.58  --inst_out_proof                        true
% 7.00/1.58  
% 7.00/1.58  ------ Resolution Options
% 7.00/1.58  
% 7.00/1.58  --resolution_flag                       false
% 7.00/1.58  --res_lit_sel                           adaptive
% 7.00/1.58  --res_lit_sel_side                      none
% 7.00/1.58  --res_ordering                          kbo
% 7.00/1.58  --res_to_prop_solver                    active
% 7.00/1.58  --res_prop_simpl_new                    false
% 7.00/1.58  --res_prop_simpl_given                  true
% 7.00/1.58  --res_passive_queue_type                priority_queues
% 7.00/1.58  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.00/1.58  --res_passive_queues_freq               [15;5]
% 7.00/1.58  --res_forward_subs                      full
% 7.00/1.58  --res_backward_subs                     full
% 7.00/1.58  --res_forward_subs_resolution           true
% 7.00/1.58  --res_backward_subs_resolution          true
% 7.00/1.58  --res_orphan_elimination                true
% 7.00/1.58  --res_time_limit                        2.
% 7.00/1.58  --res_out_proof                         true
% 7.00/1.58  
% 7.00/1.58  ------ Superposition Options
% 7.00/1.58  
% 7.00/1.58  --superposition_flag                    true
% 7.00/1.58  --sup_passive_queue_type                priority_queues
% 7.00/1.58  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.00/1.58  --sup_passive_queues_freq               [8;1;4]
% 7.00/1.58  --demod_completeness_check              fast
% 7.00/1.58  --demod_use_ground                      true
% 7.00/1.58  --sup_to_prop_solver                    passive
% 7.00/1.58  --sup_prop_simpl_new                    true
% 7.00/1.58  --sup_prop_simpl_given                  true
% 7.00/1.58  --sup_fun_splitting                     false
% 7.00/1.58  --sup_smt_interval                      50000
% 7.00/1.58  
% 7.00/1.58  ------ Superposition Simplification Setup
% 7.00/1.58  
% 7.00/1.58  --sup_indices_passive                   []
% 7.00/1.58  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.00/1.58  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.00/1.58  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.00/1.58  --sup_full_triv                         [TrivRules;PropSubs]
% 7.00/1.58  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.00/1.58  --sup_full_bw                           [BwDemod]
% 7.00/1.58  --sup_immed_triv                        [TrivRules]
% 7.00/1.58  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.00/1.58  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.00/1.58  --sup_immed_bw_main                     []
% 7.00/1.58  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.00/1.58  --sup_input_triv                        [Unflattening;TrivRules]
% 7.00/1.58  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.00/1.58  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.00/1.58  
% 7.00/1.58  ------ Combination Options
% 7.00/1.58  
% 7.00/1.58  --comb_res_mult                         3
% 7.00/1.58  --comb_sup_mult                         2
% 7.00/1.58  --comb_inst_mult                        10
% 7.00/1.58  
% 7.00/1.58  ------ Debug Options
% 7.00/1.58  
% 7.00/1.58  --dbg_backtrace                         false
% 7.00/1.58  --dbg_dump_prop_clauses                 false
% 7.00/1.58  --dbg_dump_prop_clauses_file            -
% 7.00/1.58  --dbg_out_stat                          false
% 7.00/1.58  
% 7.00/1.58  
% 7.00/1.58  
% 7.00/1.58  
% 7.00/1.58  ------ Proving...
% 7.00/1.58  
% 7.00/1.58  
% 7.00/1.58  % SZS status Theorem for theBenchmark.p
% 7.00/1.58  
% 7.00/1.58   Resolution empty clause
% 7.00/1.58  
% 7.00/1.58  % SZS output start CNFRefutation for theBenchmark.p
% 7.00/1.58  
% 7.00/1.58  fof(f12,conjecture,(
% 7.00/1.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f13,negated_conjecture,(
% 7.00/1.58    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.00/1.58    inference(negated_conjecture,[],[f12])).
% 7.00/1.58  
% 7.00/1.58  fof(f27,plain,(
% 7.00/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.00/1.58    inference(ennf_transformation,[],[f13])).
% 7.00/1.58  
% 7.00/1.58  fof(f28,plain,(
% 7.00/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.00/1.58    inference(flattening,[],[f27])).
% 7.00/1.58  
% 7.00/1.58  fof(f44,plain,(
% 7.00/1.58    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 7.00/1.58    introduced(choice_axiom,[])).
% 7.00/1.58  
% 7.00/1.58  fof(f43,plain,(
% 7.00/1.58    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 7.00/1.58    introduced(choice_axiom,[])).
% 7.00/1.58  
% 7.00/1.58  fof(f42,plain,(
% 7.00/1.58    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 7.00/1.58    introduced(choice_axiom,[])).
% 7.00/1.58  
% 7.00/1.58  fof(f41,plain,(
% 7.00/1.58    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.00/1.58    introduced(choice_axiom,[])).
% 7.00/1.58  
% 7.00/1.58  fof(f40,plain,(
% 7.00/1.58    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 7.00/1.58    introduced(choice_axiom,[])).
% 7.00/1.58  
% 7.00/1.58  fof(f39,plain,(
% 7.00/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 7.00/1.58    introduced(choice_axiom,[])).
% 7.00/1.58  
% 7.00/1.58  fof(f45,plain,(
% 7.00/1.58    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.00/1.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f44,f43,f42,f41,f40,f39])).
% 7.00/1.58  
% 7.00/1.58  fof(f78,plain,(
% 7.00/1.58    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f8,axiom,(
% 7.00/1.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f20,plain,(
% 7.00/1.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.00/1.58    inference(ennf_transformation,[],[f8])).
% 7.00/1.58  
% 7.00/1.58  fof(f58,plain,(
% 7.00/1.58    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.00/1.58    inference(cnf_transformation,[],[f20])).
% 7.00/1.58  
% 7.00/1.58  fof(f3,axiom,(
% 7.00/1.58    v1_xboole_0(k1_xboole_0)),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f50,plain,(
% 7.00/1.58    v1_xboole_0(k1_xboole_0)),
% 7.00/1.58    inference(cnf_transformation,[],[f3])).
% 7.00/1.58  
% 7.00/1.58  fof(f4,axiom,(
% 7.00/1.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f14,plain,(
% 7.00/1.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.00/1.58    inference(rectify,[],[f4])).
% 7.00/1.58  
% 7.00/1.58  fof(f15,plain,(
% 7.00/1.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.00/1.58    inference(ennf_transformation,[],[f14])).
% 7.00/1.58  
% 7.00/1.58  fof(f34,plain,(
% 7.00/1.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.00/1.58    introduced(choice_axiom,[])).
% 7.00/1.58  
% 7.00/1.58  fof(f35,plain,(
% 7.00/1.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.00/1.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f34])).
% 7.00/1.58  
% 7.00/1.58  fof(f51,plain,(
% 7.00/1.58    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f35])).
% 7.00/1.58  
% 7.00/1.58  fof(f1,axiom,(
% 7.00/1.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f29,plain,(
% 7.00/1.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.00/1.58    inference(nnf_transformation,[],[f1])).
% 7.00/1.58  
% 7.00/1.58  fof(f30,plain,(
% 7.00/1.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.00/1.58    inference(rectify,[],[f29])).
% 7.00/1.58  
% 7.00/1.58  fof(f31,plain,(
% 7.00/1.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.00/1.58    introduced(choice_axiom,[])).
% 7.00/1.58  
% 7.00/1.58  fof(f32,plain,(
% 7.00/1.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.00/1.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.00/1.58  
% 7.00/1.58  fof(f46,plain,(
% 7.00/1.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f32])).
% 7.00/1.58  
% 7.00/1.58  fof(f2,axiom,(
% 7.00/1.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f33,plain,(
% 7.00/1.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.00/1.58    inference(nnf_transformation,[],[f2])).
% 7.00/1.58  
% 7.00/1.58  fof(f48,plain,(
% 7.00/1.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f33])).
% 7.00/1.58  
% 7.00/1.58  fof(f49,plain,(
% 7.00/1.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.00/1.58    inference(cnf_transformation,[],[f33])).
% 7.00/1.58  
% 7.00/1.58  fof(f6,axiom,(
% 7.00/1.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f17,plain,(
% 7.00/1.58    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.00/1.58    inference(ennf_transformation,[],[f6])).
% 7.00/1.58  
% 7.00/1.58  fof(f55,plain,(
% 7.00/1.58    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f17])).
% 7.00/1.58  
% 7.00/1.58  fof(f9,axiom,(
% 7.00/1.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f21,plain,(
% 7.00/1.58    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.00/1.58    inference(ennf_transformation,[],[f9])).
% 7.00/1.58  
% 7.00/1.58  fof(f22,plain,(
% 7.00/1.58    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.00/1.58    inference(flattening,[],[f21])).
% 7.00/1.58  
% 7.00/1.58  fof(f59,plain,(
% 7.00/1.58    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f22])).
% 7.00/1.58  
% 7.00/1.58  fof(f76,plain,(
% 7.00/1.58    v1_funct_1(sK7)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f71,plain,(
% 7.00/1.58    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f5,axiom,(
% 7.00/1.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f16,plain,(
% 7.00/1.58    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.00/1.58    inference(ennf_transformation,[],[f5])).
% 7.00/1.58  
% 7.00/1.58  fof(f54,plain,(
% 7.00/1.58    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.00/1.58    inference(cnf_transformation,[],[f16])).
% 7.00/1.58  
% 7.00/1.58  fof(f79,plain,(
% 7.00/1.58    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f7,axiom,(
% 7.00/1.58    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f18,plain,(
% 7.00/1.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.00/1.58    inference(ennf_transformation,[],[f7])).
% 7.00/1.58  
% 7.00/1.58  fof(f19,plain,(
% 7.00/1.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.00/1.58    inference(flattening,[],[f18])).
% 7.00/1.58  
% 7.00/1.58  fof(f36,plain,(
% 7.00/1.58    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.00/1.58    inference(nnf_transformation,[],[f19])).
% 7.00/1.58  
% 7.00/1.58  fof(f56,plain,(
% 7.00/1.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f36])).
% 7.00/1.58  
% 7.00/1.58  fof(f72,plain,(
% 7.00/1.58    r1_subset_1(sK4,sK5)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f68,plain,(
% 7.00/1.58    ~v1_xboole_0(sK4)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f70,plain,(
% 7.00/1.58    ~v1_xboole_0(sK5)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f75,plain,(
% 7.00/1.58    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f73,plain,(
% 7.00/1.58    v1_funct_1(sK6)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f10,axiom,(
% 7.00/1.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f23,plain,(
% 7.00/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.00/1.58    inference(ennf_transformation,[],[f10])).
% 7.00/1.58  
% 7.00/1.58  fof(f24,plain,(
% 7.00/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.00/1.58    inference(flattening,[],[f23])).
% 7.00/1.58  
% 7.00/1.58  fof(f37,plain,(
% 7.00/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.00/1.58    inference(nnf_transformation,[],[f24])).
% 7.00/1.58  
% 7.00/1.58  fof(f38,plain,(
% 7.00/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.00/1.58    inference(flattening,[],[f37])).
% 7.00/1.58  
% 7.00/1.58  fof(f60,plain,(
% 7.00/1.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f38])).
% 7.00/1.58  
% 7.00/1.58  fof(f83,plain,(
% 7.00/1.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.00/1.58    inference(equality_resolution,[],[f60])).
% 7.00/1.58  
% 7.00/1.58  fof(f11,axiom,(
% 7.00/1.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.00/1.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.00/1.58  
% 7.00/1.58  fof(f25,plain,(
% 7.00/1.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.00/1.58    inference(ennf_transformation,[],[f11])).
% 7.00/1.58  
% 7.00/1.58  fof(f26,plain,(
% 7.00/1.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.00/1.58    inference(flattening,[],[f25])).
% 7.00/1.58  
% 7.00/1.58  fof(f63,plain,(
% 7.00/1.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f26])).
% 7.00/1.58  
% 7.00/1.58  fof(f64,plain,(
% 7.00/1.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f26])).
% 7.00/1.58  
% 7.00/1.58  fof(f65,plain,(
% 7.00/1.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f26])).
% 7.00/1.58  
% 7.00/1.58  fof(f67,plain,(
% 7.00/1.58    ~v1_xboole_0(sK3)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f77,plain,(
% 7.00/1.58    v1_funct_2(sK7,sK5,sK3)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f74,plain,(
% 7.00/1.58    v1_funct_2(sK6,sK4,sK3)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f66,plain,(
% 7.00/1.58    ~v1_xboole_0(sK2)),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f69,plain,(
% 7.00/1.58    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 7.00/1.58    inference(cnf_transformation,[],[f45])).
% 7.00/1.58  
% 7.00/1.58  fof(f61,plain,(
% 7.00/1.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.00/1.58    inference(cnf_transformation,[],[f38])).
% 7.00/1.58  
% 7.00/1.58  fof(f82,plain,(
% 7.00/1.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.00/1.58    inference(equality_resolution,[],[f61])).
% 7.00/1.58  
% 7.00/1.58  cnf(c_21,negated_conjecture,
% 7.00/1.58      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.00/1.58      inference(cnf_transformation,[],[f78]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1099,negated_conjecture,
% 7.00/1.58      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_21]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1917,plain,
% 7.00/1.58      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_12,plain,
% 7.00/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.00/1.58      inference(cnf_transformation,[],[f58]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1106,plain,
% 7.00/1.58      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.00/1.58      | v1_relat_1(X0_54) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_12]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1911,plain,
% 7.00/1.58      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.00/1.58      | v1_relat_1(X0_54) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3256,plain,
% 7.00/1.58      ( v1_relat_1(sK7) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1917,c_1911]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_4,plain,
% 7.00/1.58      ( v1_xboole_0(k1_xboole_0) ),
% 7.00/1.58      inference(cnf_transformation,[],[f50]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1112,plain,
% 7.00/1.58      ( v1_xboole_0(k1_xboole_0) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_4]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1905,plain,
% 7.00/1.58      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1112]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_7,plain,
% 7.00/1.58      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.00/1.58      inference(cnf_transformation,[],[f51]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1109,plain,
% 7.00/1.58      ( r1_xboole_0(X0_54,X1_54) | r2_hidden(sK1(X0_54,X1_54),X0_54) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_7]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1908,plain,
% 7.00/1.58      ( r1_xboole_0(X0_54,X1_54) = iProver_top
% 7.00/1.58      | r2_hidden(sK1(X0_54,X1_54),X0_54) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1,plain,
% 7.00/1.58      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.00/1.58      inference(cnf_transformation,[],[f46]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1115,plain,
% 7.00/1.58      ( ~ r2_hidden(X0_56,X0_54) | ~ v1_xboole_0(X0_54) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_1]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1902,plain,
% 7.00/1.58      ( r2_hidden(X0_56,X0_54) != iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) != iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1115]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3251,plain,
% 7.00/1.58      ( r1_xboole_0(X0_54,X1_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) != iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1908,c_1902]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3,plain,
% 7.00/1.58      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.00/1.58      inference(cnf_transformation,[],[f48]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1113,plain,
% 7.00/1.58      ( ~ r1_xboole_0(X0_54,X1_54) | k3_xboole_0(X0_54,X1_54) = k1_xboole_0 ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_3]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1904,plain,
% 7.00/1.58      ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
% 7.00/1.58      | r1_xboole_0(X0_54,X1_54) != iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_5110,plain,
% 7.00/1.58      ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
% 7.00/1.58      | v1_xboole_0(X0_54) != iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_3251,c_1904]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6105,plain,
% 7.00/1.58      ( k3_xboole_0(k1_xboole_0,X0_54) = k1_xboole_0 ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1905,c_5110]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2,plain,
% 7.00/1.58      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.00/1.58      inference(cnf_transformation,[],[f49]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1114,plain,
% 7.00/1.58      ( r1_xboole_0(X0_54,X1_54) | k3_xboole_0(X0_54,X1_54) != k1_xboole_0 ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_2]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1903,plain,
% 7.00/1.58      ( k3_xboole_0(X0_54,X1_54) != k1_xboole_0
% 7.00/1.58      | r1_xboole_0(X0_54,X1_54) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6139,plain,
% 7.00/1.58      ( r1_xboole_0(k1_xboole_0,X0_54) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_6105,c_1903]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_9,plain,
% 7.00/1.58      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.00/1.58      | ~ v1_relat_1(X1)
% 7.00/1.58      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.00/1.58      inference(cnf_transformation,[],[f55]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1107,plain,
% 7.00/1.58      ( ~ r1_xboole_0(X0_54,k1_relat_1(X1_54))
% 7.00/1.58      | ~ v1_relat_1(X1_54)
% 7.00/1.58      | k7_relat_1(X1_54,X0_54) = k1_xboole_0 ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_9]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1910,plain,
% 7.00/1.58      ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 7.00/1.58      | r1_xboole_0(X1_54,k1_relat_1(X0_54)) != iProver_top
% 7.00/1.58      | v1_relat_1(X0_54) != iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1107]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6153,plain,
% 7.00/1.58      ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
% 7.00/1.58      | v1_relat_1(X0_54) != iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_6139,c_1910]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_7310,plain,
% 7.00/1.58      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_3256,c_6153]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_13,plain,
% 7.00/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.58      | ~ v1_funct_1(X0)
% 7.00/1.58      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.00/1.58      inference(cnf_transformation,[],[f59]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1105,plain,
% 7.00/1.58      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.00/1.58      | ~ v1_funct_1(X0_54)
% 7.00/1.58      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_13]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1912,plain,
% 7.00/1.58      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.00/1.58      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.00/1.58      | v1_funct_1(X2_54) != iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1105]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3519,plain,
% 7.00/1.58      ( k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54)
% 7.00/1.58      | v1_funct_1(sK7) != iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1917,c_1912]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_23,negated_conjecture,
% 7.00/1.58      ( v1_funct_1(sK7) ),
% 7.00/1.58      inference(cnf_transformation,[],[f76]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2348,plain,
% 7.00/1.58      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.00/1.58      | ~ v1_funct_1(sK7)
% 7.00/1.58      | k2_partfun1(X0_54,X1_54,sK7,X2_54) = k7_relat_1(sK7,X2_54) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_1105]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2537,plain,
% 7.00/1.58      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
% 7.00/1.58      | ~ v1_funct_1(sK7)
% 7.00/1.58      | k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_2348]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3942,plain,
% 7.00/1.58      ( k2_partfun1(sK5,sK3,sK7,X0_54) = k7_relat_1(sK7,X0_54) ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_3519,c_23,c_21,c_2537]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_28,negated_conjecture,
% 7.00/1.58      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.00/1.58      inference(cnf_transformation,[],[f71]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1093,negated_conjecture,
% 7.00/1.58      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_28]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1923,plain,
% 7.00/1.58      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1093]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_8,plain,
% 7.00/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.00/1.58      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.00/1.58      inference(cnf_transformation,[],[f54]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1108,plain,
% 7.00/1.58      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.00/1.58      | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_8]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1909,plain,
% 7.00/1.58      ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
% 7.00/1.58      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3179,plain,
% 7.00/1.58      ( k9_subset_1(sK2,X0_54,sK5) = k3_xboole_0(X0_54,sK5) ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1923,c_1909]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_20,negated_conjecture,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.00/1.58      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.00/1.58      inference(cnf_transformation,[],[f79]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1100,negated_conjecture,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.00/1.58      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_20]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3353,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.00/1.58      | k2_partfun1(sK5,sK3,sK7,k3_xboole_0(sK4,sK5)) != k2_partfun1(sK4,sK3,sK6,k3_xboole_0(sK4,sK5)) ),
% 7.00/1.58      inference(demodulation,[status(thm)],[c_3179,c_1100]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_11,plain,
% 7.00/1.58      ( ~ r1_subset_1(X0,X1)
% 7.00/1.58      | r1_xboole_0(X0,X1)
% 7.00/1.58      | v1_xboole_0(X0)
% 7.00/1.58      | v1_xboole_0(X1) ),
% 7.00/1.58      inference(cnf_transformation,[],[f56]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_27,negated_conjecture,
% 7.00/1.58      ( r1_subset_1(sK4,sK5) ),
% 7.00/1.58      inference(cnf_transformation,[],[f72]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_458,plain,
% 7.00/1.58      ( r1_xboole_0(X0,X1)
% 7.00/1.58      | v1_xboole_0(X0)
% 7.00/1.58      | v1_xboole_0(X1)
% 7.00/1.58      | sK5 != X1
% 7.00/1.58      | sK4 != X0 ),
% 7.00/1.58      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_459,plain,
% 7.00/1.58      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 7.00/1.58      inference(unflattening,[status(thm)],[c_458]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_31,negated_conjecture,
% 7.00/1.58      ( ~ v1_xboole_0(sK4) ),
% 7.00/1.58      inference(cnf_transformation,[],[f68]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_29,negated_conjecture,
% 7.00/1.58      ( ~ v1_xboole_0(sK5) ),
% 7.00/1.58      inference(cnf_transformation,[],[f70]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_461,plain,
% 7.00/1.58      ( r1_xboole_0(sK4,sK5) ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_459,c_31,c_29]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1085,plain,
% 7.00/1.58      ( r1_xboole_0(sK4,sK5) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_461]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1931,plain,
% 7.00/1.58      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2820,plain,
% 7.00/1.58      ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1931,c_1904]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3354,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.00/1.58      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k2_partfun1(sK5,sK3,sK7,k1_xboole_0) ),
% 7.00/1.58      inference(light_normalisation,[status(thm)],[c_3353,c_2820]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3946,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.00/1.58      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.00/1.58      inference(demodulation,[status(thm)],[c_3942,c_3354]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_24,negated_conjecture,
% 7.00/1.58      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.00/1.58      inference(cnf_transformation,[],[f75]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1096,negated_conjecture,
% 7.00/1.58      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_24]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1920,plain,
% 7.00/1.58      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3520,plain,
% 7.00/1.58      ( k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54)
% 7.00/1.58      | v1_funct_1(sK6) != iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1920,c_1912]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_26,negated_conjecture,
% 7.00/1.58      ( v1_funct_1(sK6) ),
% 7.00/1.58      inference(cnf_transformation,[],[f73]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2353,plain,
% 7.00/1.58      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.00/1.58      | ~ v1_funct_1(sK6)
% 7.00/1.58      | k2_partfun1(X0_54,X1_54,sK6,X2_54) = k7_relat_1(sK6,X2_54) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_1105]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2542,plain,
% 7.00/1.58      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.00/1.58      | ~ v1_funct_1(sK6)
% 7.00/1.58      | k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_2353]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3948,plain,
% 7.00/1.58      ( k2_partfun1(sK4,sK3,sK6,X0_54) = k7_relat_1(sK6,X0_54) ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_3520,c_26,c_24,c_2542]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_4038,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.00/1.58      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.00/1.58      inference(demodulation,[status(thm)],[c_3946,c_3948]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_7749,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 7.00/1.58      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 7.00/1.58      inference(demodulation,[status(thm)],[c_7310,c_4038]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2269,plain,
% 7.00/1.58      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 7.00/1.58      | v1_relat_1(sK6) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_1106]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2467,plain,
% 7.00/1.58      ( r1_xboole_0(k1_xboole_0,X0_54)
% 7.00/1.58      | r2_hidden(sK1(k1_xboole_0,X0_54),k1_xboole_0) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_1109]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2796,plain,
% 7.00/1.58      ( r1_xboole_0(k1_xboole_0,k1_relat_1(sK6))
% 7.00/1.58      | r2_hidden(sK1(k1_xboole_0,k1_relat_1(sK6)),k1_xboole_0) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_2467]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2455,plain,
% 7.00/1.58      ( ~ r1_xboole_0(X0_54,k1_relat_1(sK6))
% 7.00/1.58      | ~ v1_relat_1(sK6)
% 7.00/1.58      | k7_relat_1(sK6,X0_54) = k1_xboole_0 ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_1107]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2797,plain,
% 7.00/1.58      ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK6))
% 7.00/1.58      | ~ v1_relat_1(sK6)
% 7.00/1.58      | k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_2455]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2257,plain,
% 7.00/1.58      ( ~ r2_hidden(X0_56,k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_1115]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_2466,plain,
% 7.00/1.58      ( ~ r2_hidden(sK1(k1_xboole_0,X0_54),k1_xboole_0)
% 7.00/1.58      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_2257]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3697,plain,
% 7.00/1.58      ( ~ r2_hidden(sK1(k1_xboole_0,k1_relat_1(sK6)),k1_xboole_0)
% 7.00/1.58      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.00/1.58      inference(instantiation,[status(thm)],[c_2466]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_16,plain,
% 7.00/1.58      ( ~ v1_funct_2(X0,X1,X2)
% 7.00/1.58      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.58      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.00/1.58      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.58      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.58      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.00/1.58      | ~ v1_funct_1(X0)
% 7.00/1.58      | ~ v1_funct_1(X3)
% 7.00/1.58      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.00/1.58      | v1_xboole_0(X5)
% 7.00/1.58      | v1_xboole_0(X4)
% 7.00/1.58      | v1_xboole_0(X2)
% 7.00/1.58      | v1_xboole_0(X1)
% 7.00/1.58      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.00/1.58      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.00/1.58      inference(cnf_transformation,[],[f83]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_19,plain,
% 7.00/1.58      ( ~ v1_funct_2(X0,X1,X2)
% 7.00/1.58      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.58      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.58      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.58      | ~ v1_funct_1(X0)
% 7.00/1.58      | ~ v1_funct_1(X3)
% 7.00/1.58      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.00/1.58      | v1_xboole_0(X5)
% 7.00/1.58      | v1_xboole_0(X4)
% 7.00/1.58      | v1_xboole_0(X2)
% 7.00/1.58      | v1_xboole_0(X1) ),
% 7.00/1.58      inference(cnf_transformation,[],[f63]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_18,plain,
% 7.00/1.58      ( ~ v1_funct_2(X0,X1,X2)
% 7.00/1.58      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.58      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.00/1.58      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.58      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.58      | ~ v1_funct_1(X0)
% 7.00/1.58      | ~ v1_funct_1(X3)
% 7.00/1.58      | v1_xboole_0(X5)
% 7.00/1.58      | v1_xboole_0(X4)
% 7.00/1.58      | v1_xboole_0(X2)
% 7.00/1.58      | v1_xboole_0(X1) ),
% 7.00/1.58      inference(cnf_transformation,[],[f64]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_17,plain,
% 7.00/1.58      ( ~ v1_funct_2(X0,X1,X2)
% 7.00/1.58      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.58      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.58      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.58      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.00/1.58      | ~ v1_funct_1(X0)
% 7.00/1.58      | ~ v1_funct_1(X3)
% 7.00/1.58      | v1_xboole_0(X5)
% 7.00/1.58      | v1_xboole_0(X4)
% 7.00/1.58      | v1_xboole_0(X2)
% 7.00/1.58      | v1_xboole_0(X1) ),
% 7.00/1.58      inference(cnf_transformation,[],[f65]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_182,plain,
% 7.00/1.58      ( ~ v1_funct_1(X3)
% 7.00/1.58      | ~ v1_funct_1(X0)
% 7.00/1.58      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.58      | ~ v1_funct_2(X0,X1,X2)
% 7.00/1.58      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.58      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.58      | v1_xboole_0(X5)
% 7.00/1.58      | v1_xboole_0(X4)
% 7.00/1.58      | v1_xboole_0(X2)
% 7.00/1.58      | v1_xboole_0(X1)
% 7.00/1.58      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.00/1.58      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_16,c_19,c_18,c_17]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_183,plain,
% 7.00/1.58      ( ~ v1_funct_2(X0,X1,X2)
% 7.00/1.58      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.58      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.58      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.58      | ~ v1_funct_1(X0)
% 7.00/1.58      | ~ v1_funct_1(X3)
% 7.00/1.58      | v1_xboole_0(X1)
% 7.00/1.58      | v1_xboole_0(X2)
% 7.00/1.58      | v1_xboole_0(X4)
% 7.00/1.58      | v1_xboole_0(X5)
% 7.00/1.58      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.00/1.58      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.00/1.58      inference(renaming,[status(thm)],[c_182]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1087,plain,
% 7.00/1.58      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.00/1.58      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.00/1.58      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.00/1.58      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.00/1.58      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.00/1.58      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.00/1.58      | ~ v1_funct_1(X0_54)
% 7.00/1.58      | ~ v1_funct_1(X3_54)
% 7.00/1.58      | v1_xboole_0(X1_54)
% 7.00/1.58      | v1_xboole_0(X2_54)
% 7.00/1.58      | v1_xboole_0(X4_54)
% 7.00/1.58      | v1_xboole_0(X5_54)
% 7.00/1.58      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.00/1.58      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_183]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1929,plain,
% 7.00/1.58      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.00/1.58      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 7.00/1.58      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.00/1.58      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.00/1.58      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.00/1.58      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.00/1.58      | v1_funct_1(X2_54) != iProver_top
% 7.00/1.58      | v1_funct_1(X5_54) != iProver_top
% 7.00/1.58      | v1_xboole_0(X3_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X4_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X1_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1087]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_5697,plain,
% 7.00/1.58      ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.00/1.58      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
% 7.00/1.58      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.58      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.00/1.58      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.58      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.58      | v1_funct_1(X1_54) != iProver_top
% 7.00/1.58      | v1_funct_1(sK7) != iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X2_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(sK3) = iProver_top
% 7.00/1.58      | v1_xboole_0(sK5) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_3942,c_1929]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_32,negated_conjecture,
% 7.00/1.58      ( ~ v1_xboole_0(sK3) ),
% 7.00/1.58      inference(cnf_transformation,[],[f67]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_35,plain,
% 7.00/1.58      ( v1_xboole_0(sK3) != iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_38,plain,
% 7.00/1.58      ( v1_xboole_0(sK5) != iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_44,plain,
% 7.00/1.58      ( v1_funct_1(sK7) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_22,negated_conjecture,
% 7.00/1.58      ( v1_funct_2(sK7,sK5,sK3) ),
% 7.00/1.58      inference(cnf_transformation,[],[f77]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_45,plain,
% 7.00/1.58      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_46,plain,
% 7.00/1.58      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6186,plain,
% 7.00/1.58      ( v1_funct_1(X1_54) != iProver_top
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.58      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.58      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
% 7.00/1.58      | k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.00/1.58      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X2_54) = iProver_top ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_5697,c_35,c_38,c_44,c_45,c_46]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6187,plain,
% 7.00/1.58      ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.00/1.58      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),X0_54) = X1_54
% 7.00/1.58      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.58      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.58      | v1_funct_1(X1_54) != iProver_top
% 7.00/1.58      | v1_xboole_0(X2_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.58      inference(renaming,[status(thm)],[c_6186]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6202,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.00/1.58      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.00/1.58      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | v1_funct_1(sK6) != iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(sK4) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_3948,c_6187]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_36,plain,
% 7.00/1.58      ( v1_xboole_0(sK4) != iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_41,plain,
% 7.00/1.58      ( v1_funct_1(sK6) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_25,negated_conjecture,
% 7.00/1.58      ( v1_funct_2(sK6,sK4,sK3) ),
% 7.00/1.58      inference(cnf_transformation,[],[f74]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_42,plain,
% 7.00/1.58      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_43,plain,
% 7.00/1.58      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6303,plain,
% 7.00/1.58      ( v1_xboole_0(X0_54) = iProver_top
% 7.00/1.58      | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_6202,c_36,c_41,c_42,c_43]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6304,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.58      inference(renaming,[status(thm)],[c_6303]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6314,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.58      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_3179,c_6304]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6315,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.58      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.58      inference(light_normalisation,[status(thm)],[c_6314,c_2820]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6316,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.58      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.58      inference(demodulation,[status(thm)],[c_6315,c_3179]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6317,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.58      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.58      inference(light_normalisation,[status(thm)],[c_6316,c_2820]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_33,negated_conjecture,
% 7.00/1.58      ( ~ v1_xboole_0(sK2) ),
% 7.00/1.58      inference(cnf_transformation,[],[f66]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_30,negated_conjecture,
% 7.00/1.58      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 7.00/1.58      inference(cnf_transformation,[],[f69]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_6318,plain,
% 7.00/1.58      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 7.00/1.58      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 7.00/1.58      | v1_xboole_0(sK2)
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.00/1.58      inference(predicate_to_equality_rev,[status(thm)],[c_6317]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_17308,plain,
% 7.00/1.58      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
% 7.00/1.58      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_6317,c_33,c_30,c_28,c_6318]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_17309,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 7.00/1.58      inference(renaming,[status(thm)],[c_17308]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3257,plain,
% 7.00/1.58      ( v1_relat_1(sK6) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1920,c_1911]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_7311,plain,
% 7.00/1.58      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_3257,c_6153]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_17310,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 7.00/1.58      | k1_xboole_0 != k1_xboole_0 ),
% 7.00/1.58      inference(light_normalisation,[status(thm)],[c_17309,c_7310,c_7311]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_17311,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
% 7.00/1.58      inference(equality_resolution_simp,[status(thm)],[c_17310]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_19186,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_7749,c_24,c_4,c_2269,c_2796,c_2797,c_3697,c_17311]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1103,plain,
% 7.00/1.58      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.00/1.58      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.00/1.58      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.00/1.58      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.00/1.58      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.00/1.58      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.00/1.58      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
% 7.00/1.58      | ~ v1_funct_1(X0_54)
% 7.00/1.58      | ~ v1_funct_1(X3_54)
% 7.00/1.58      | v1_xboole_0(X1_54)
% 7.00/1.58      | v1_xboole_0(X2_54)
% 7.00/1.58      | v1_xboole_0(X4_54)
% 7.00/1.58      | v1_xboole_0(X5_54) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_17]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1914,plain,
% 7.00/1.58      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.00/1.58      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.00/1.58      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.00/1.58      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.00/1.58      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
% 7.00/1.58      | v1_funct_1(X0_54) != iProver_top
% 7.00/1.58      | v1_funct_1(X3_54) != iProver_top
% 7.00/1.58      | v1_xboole_0(X5_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X4_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X2_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X1_54) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1103]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_3729,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.00/1.58      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.00/1.58      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.00/1.58      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.00/1.58      | v1_funct_1(X5_54) != iProver_top
% 7.00/1.58      | v1_funct_1(X4_54) != iProver_top
% 7.00/1.58      | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X1_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X3_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X2_54) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1914,c_1912]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1101,plain,
% 7.00/1.58      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.00/1.58      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.00/1.58      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.00/1.58      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.00/1.58      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.00/1.58      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.00/1.58      | ~ v1_funct_1(X0_54)
% 7.00/1.58      | ~ v1_funct_1(X3_54)
% 7.00/1.58      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
% 7.00/1.58      | v1_xboole_0(X1_54)
% 7.00/1.58      | v1_xboole_0(X2_54)
% 7.00/1.58      | v1_xboole_0(X4_54)
% 7.00/1.58      | v1_xboole_0(X5_54) ),
% 7.00/1.58      inference(subtyping,[status(esa)],[c_19]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_1916,plain,
% 7.00/1.58      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.00/1.58      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.00/1.58      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.00/1.58      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.00/1.58      | v1_funct_1(X0_54) != iProver_top
% 7.00/1.58      | v1_funct_1(X3_54) != iProver_top
% 7.00/1.58      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
% 7.00/1.58      | v1_xboole_0(X5_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X4_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X2_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X1_54) = iProver_top ),
% 7.00/1.58      inference(predicate_to_equality,[status(thm)],[c_1101]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_11873,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.00/1.58      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.00/1.58      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.00/1.58      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.00/1.58      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.00/1.58      | v1_funct_1(X5_54) != iProver_top
% 7.00/1.58      | v1_funct_1(X4_54) != iProver_top
% 7.00/1.58      | v1_xboole_0(X2_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X1_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X3_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.58      inference(forward_subsumption_resolution,[status(thm)],[c_3729,c_1916]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_11877,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
% 7.00/1.58      | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
% 7.00/1.58      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | v1_funct_1(X2_54) != iProver_top
% 7.00/1.58      | v1_funct_1(sK7) != iProver_top
% 7.00/1.58      | v1_xboole_0(X1_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(sK3) = iProver_top
% 7.00/1.58      | v1_xboole_0(sK5) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1917,c_11873]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_11984,plain,
% 7.00/1.58      ( v1_funct_1(X2_54) != iProver_top
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
% 7.00/1.58      | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
% 7.00/1.58      | v1_xboole_0(X1_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_11877,c_35,c_38,c_44,c_45]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_11985,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK5),sK3,k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,X1_54,sK5,X2_54,sK7),X3_54)
% 7.00/1.58      | v1_funct_2(X2_54,X1_54,sK3) != iProver_top
% 7.00/1.58      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK3))) != iProver_top
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | v1_funct_1(X2_54) != iProver_top
% 7.00/1.58      | v1_xboole_0(X1_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.58      inference(renaming,[status(thm)],[c_11984]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_11999,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
% 7.00/1.58      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | v1_funct_1(sK6) != iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.58      | v1_xboole_0(sK4) = iProver_top ),
% 7.00/1.58      inference(superposition,[status(thm)],[c_1920,c_11985]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_12454,plain,
% 7.00/1.58      ( v1_xboole_0(X0_54) = iProver_top
% 7.00/1.58      | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.00/1.58      inference(global_propositional_subsumption,
% 7.00/1.58                [status(thm)],
% 7.00/1.58                [c_11999,c_36,c_41,c_42]) ).
% 7.00/1.58  
% 7.00/1.58  cnf(c_12455,plain,
% 7.00/1.58      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),X1_54)
% 7.00/1.58      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.58      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.58      inference(renaming,[status(thm)],[c_12454]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_12464,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54)
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.59      inference(superposition,[status(thm)],[c_1923,c_12455]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_34,plain,
% 7.00/1.59      ( v1_xboole_0(sK2) != iProver_top ),
% 7.00/1.59      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_37,plain,
% 7.00/1.59      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.00/1.59      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_12469,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) = k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_54) ),
% 7.00/1.59      inference(global_propositional_subsumption,
% 7.00/1.59                [status(thm)],
% 7.00/1.59                [c_12464,c_34,c_37]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_15,plain,
% 7.00/1.59      ( ~ v1_funct_2(X0,X1,X2)
% 7.00/1.59      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.59      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.00/1.59      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.59      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.59      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.59      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.59      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.00/1.59      | ~ v1_funct_1(X0)
% 7.00/1.59      | ~ v1_funct_1(X3)
% 7.00/1.59      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.00/1.59      | v1_xboole_0(X5)
% 7.00/1.59      | v1_xboole_0(X4)
% 7.00/1.59      | v1_xboole_0(X2)
% 7.00/1.59      | v1_xboole_0(X1)
% 7.00/1.59      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.00/1.59      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.00/1.59      inference(cnf_transformation,[],[f82]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_189,plain,
% 7.00/1.59      ( ~ v1_funct_1(X3)
% 7.00/1.59      | ~ v1_funct_1(X0)
% 7.00/1.59      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.59      | ~ v1_funct_2(X0,X1,X2)
% 7.00/1.59      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.59      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.59      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.59      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.59      | v1_xboole_0(X5)
% 7.00/1.59      | v1_xboole_0(X4)
% 7.00/1.59      | v1_xboole_0(X2)
% 7.00/1.59      | v1_xboole_0(X1)
% 7.00/1.59      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.00/1.59      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.00/1.59      inference(global_propositional_subsumption,
% 7.00/1.59                [status(thm)],
% 7.00/1.59                [c_15,c_19,c_18,c_17]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_190,plain,
% 7.00/1.59      ( ~ v1_funct_2(X0,X1,X2)
% 7.00/1.59      | ~ v1_funct_2(X3,X4,X2)
% 7.00/1.59      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.00/1.59      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.00/1.59      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.00/1.59      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.00/1.59      | ~ v1_funct_1(X0)
% 7.00/1.59      | ~ v1_funct_1(X3)
% 7.00/1.59      | v1_xboole_0(X1)
% 7.00/1.59      | v1_xboole_0(X2)
% 7.00/1.59      | v1_xboole_0(X4)
% 7.00/1.59      | v1_xboole_0(X5)
% 7.00/1.59      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.00/1.59      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.00/1.59      inference(renaming,[status(thm)],[c_189]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_1086,plain,
% 7.00/1.59      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.00/1.59      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.00/1.59      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.00/1.59      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.00/1.59      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.00/1.59      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.00/1.59      | ~ v1_funct_1(X0_54)
% 7.00/1.59      | ~ v1_funct_1(X3_54)
% 7.00/1.59      | v1_xboole_0(X1_54)
% 7.00/1.59      | v1_xboole_0(X2_54)
% 7.00/1.59      | v1_xboole_0(X4_54)
% 7.00/1.59      | v1_xboole_0(X5_54)
% 7.00/1.59      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.00/1.59      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 7.00/1.59      inference(subtyping,[status(esa)],[c_190]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_1930,plain,
% 7.00/1.59      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.00/1.59      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 7.00/1.59      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.00/1.59      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.00/1.59      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.00/1.59      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.00/1.59      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.00/1.59      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.00/1.59      | v1_funct_1(X2_54) != iProver_top
% 7.00/1.59      | v1_funct_1(X5_54) != iProver_top
% 7.00/1.59      | v1_xboole_0(X3_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(X4_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(X1_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.59      inference(predicate_to_equality,[status(thm)],[c_1086]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_6984,plain,
% 7.00/1.59      ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.00/1.59      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.00/1.59      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.59      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.59      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.59      | v1_funct_1(X1_54) != iProver_top
% 7.00/1.59      | v1_funct_1(sK7) != iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(X2_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(sK3) = iProver_top
% 7.00/1.59      | v1_xboole_0(sK5) = iProver_top ),
% 7.00/1.59      inference(superposition,[status(thm)],[c_3942,c_1930]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14525,plain,
% 7.00/1.59      ( v1_funct_1(X1_54) != iProver_top
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.59      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.59      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.00/1.59      | k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.00/1.59      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.59      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(X2_54) = iProver_top ),
% 7.00/1.59      inference(global_propositional_subsumption,
% 7.00/1.59                [status(thm)],
% 7.00/1.59                [c_6984,c_35,c_38,c_44,c_45,c_46]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14526,plain,
% 7.00/1.59      ( k2_partfun1(X0_54,sK3,X1_54,k9_subset_1(X2_54,X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(X2_54,X0_54,sK5))
% 7.00/1.59      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK5),sK3,k1_tmap_1(X2_54,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.00/1.59      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.59      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(X2_54)) != iProver_top
% 7.00/1.59      | v1_funct_1(X1_54) != iProver_top
% 7.00/1.59      | v1_xboole_0(X2_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.59      inference(renaming,[status(thm)],[c_14525]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14546,plain,
% 7.00/1.59      ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,X0_54,sK5))
% 7.00/1.59      | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.00/1.59      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_funct_1(X1_54) != iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.59      inference(superposition,[status(thm)],[c_3179,c_14526]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14556,plain,
% 7.00/1.59      ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
% 7.00/1.59      | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.00/1.59      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_funct_1(X1_54) != iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.59      inference(light_normalisation,[status(thm)],[c_14546,c_3179]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_39,plain,
% 7.00/1.59      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.00/1.59      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14718,plain,
% 7.00/1.59      ( v1_xboole_0(X0_54) = iProver_top
% 7.00/1.59      | v1_funct_1(X1_54) != iProver_top
% 7.00/1.59      | k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
% 7.00/1.59      | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.00/1.59      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top ),
% 7.00/1.59      inference(global_propositional_subsumption,
% 7.00/1.59                [status(thm)],
% 7.00/1.59                [c_14556,c_34,c_39]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14719,plain,
% 7.00/1.59      ( k2_partfun1(X0_54,sK3,X1_54,k3_xboole_0(X0_54,sK5)) != k7_relat_1(sK7,k3_xboole_0(X0_54,sK5))
% 7.00/1.59      | k2_partfun1(k4_subset_1(sK2,X0_54,sK5),sK3,k1_tmap_1(sK2,sK3,X0_54,sK5,X1_54,sK7),sK5) = sK7
% 7.00/1.59      | v1_funct_2(X1_54,X0_54,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(X0_54,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_funct_1(X1_54) != iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.59      inference(renaming,[status(thm)],[c_14718]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14732,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.00/1.59      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_funct_1(sK6) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK4) = iProver_top ),
% 7.00/1.59      inference(superposition,[status(thm)],[c_3948,c_14719]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14817,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k1_xboole_0 != k1_xboole_0
% 7.00/1.59      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_funct_1(sK6) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK4) = iProver_top ),
% 7.00/1.59      inference(light_normalisation,
% 7.00/1.59                [status(thm)],
% 7.00/1.59                [c_14732,c_2820,c_7310,c_7311]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14818,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_funct_1(sK6) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK4) = iProver_top ),
% 7.00/1.59      inference(equality_resolution_simp,[status(thm)],[c_14817]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14819,plain,
% 7.00/1.59      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_funct_1(sK6) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK4) = iProver_top ),
% 7.00/1.59      inference(demodulation,[status(thm)],[c_14818,c_12469]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14541,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.00/1.59      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 7.00/1.59      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.59      | v1_funct_1(sK6) != iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top
% 7.00/1.59      | v1_xboole_0(sK4) = iProver_top ),
% 7.00/1.59      inference(superposition,[status(thm)],[c_3948,c_14526]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14700,plain,
% 7.00/1.59      ( v1_xboole_0(X0_54) = iProver_top
% 7.00/1.59      | k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.00/1.59      inference(global_propositional_subsumption,
% 7.00/1.59                [status(thm)],
% 7.00/1.59                [c_14541,c_36,c_41,c_42,c_43]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14701,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(X0_54,sK4,sK5),sK3,k1_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k7_relat_1(sK7,k9_subset_1(X0_54,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0_54,sK4,sK5))
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(X0_54)) != iProver_top
% 7.00/1.59      | v1_xboole_0(X0_54) = iProver_top ),
% 7.00/1.59      inference(renaming,[status(thm)],[c_14700]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14711,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k3_xboole_0(sK4,sK5))
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.59      inference(superposition,[status(thm)],[c_3179,c_14701]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14712,plain,
% 7.00/1.59      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k1_xboole_0
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.59      inference(light_normalisation,[status(thm)],[c_14711,c_2820,c_7310]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14713,plain,
% 7.00/1.59      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k7_relat_1(sK6,k3_xboole_0(sK4,sK5)) != k1_xboole_0
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.59      inference(demodulation,[status(thm)],[c_14712,c_3179,c_12469]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14714,plain,
% 7.00/1.59      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | k1_xboole_0 != k1_xboole_0
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.59      inference(light_normalisation,[status(thm)],[c_14713,c_2820,c_7311]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_14715,plain,
% 7.00/1.59      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 7.00/1.59      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 7.00/1.59      | v1_xboole_0(sK2) = iProver_top ),
% 7.00/1.59      inference(equality_resolution_simp,[status(thm)],[c_14714]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_15058,plain,
% 7.00/1.59      ( k7_relat_1(k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
% 7.00/1.59      inference(global_propositional_subsumption,
% 7.00/1.59                [status(thm)],
% 7.00/1.59                [c_14819,c_34,c_37,c_39,c_14715]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_19188,plain,
% 7.00/1.59      ( sK7 != sK7 ),
% 7.00/1.59      inference(demodulation,[status(thm)],[c_19186,c_12469,c_15058]) ).
% 7.00/1.59  
% 7.00/1.59  cnf(c_19189,plain,
% 7.00/1.59      ( $false ),
% 7.00/1.59      inference(equality_resolution_simp,[status(thm)],[c_19188]) ).
% 7.00/1.59  
% 7.00/1.59  
% 7.00/1.59  % SZS output end CNFRefutation for theBenchmark.p
% 7.00/1.59  
% 7.00/1.59  ------                               Statistics
% 7.00/1.59  
% 7.00/1.59  ------ General
% 7.00/1.59  
% 7.00/1.59  abstr_ref_over_cycles:                  0
% 7.00/1.59  abstr_ref_under_cycles:                 0
% 7.00/1.59  gc_basic_clause_elim:                   0
% 7.00/1.59  forced_gc_time:                         0
% 7.00/1.59  parsing_time:                           0.033
% 7.00/1.59  unif_index_cands_time:                  0.
% 7.00/1.59  unif_index_add_time:                    0.
% 7.00/1.59  orderings_time:                         0.
% 7.00/1.59  out_proof_time:                         0.018
% 7.00/1.59  total_time:                             1.03
% 7.00/1.59  num_of_symbols:                         60
% 7.00/1.59  num_of_terms:                           33833
% 7.00/1.59  
% 7.00/1.59  ------ Preprocessing
% 7.00/1.59  
% 7.00/1.59  num_of_splits:                          0
% 7.00/1.59  num_of_split_atoms:                     0
% 7.00/1.59  num_of_reused_defs:                     0
% 7.00/1.59  num_eq_ax_congr_red:                    31
% 7.00/1.59  num_of_sem_filtered_clauses:            1
% 7.00/1.59  num_of_subtypes:                        3
% 7.00/1.59  monotx_restored_types:                  0
% 7.00/1.59  sat_num_of_epr_types:                   0
% 7.00/1.59  sat_num_of_non_cyclic_types:            0
% 7.00/1.59  sat_guarded_non_collapsed_types:        1
% 7.00/1.59  num_pure_diseq_elim:                    0
% 7.00/1.59  simp_replaced_by:                       0
% 7.00/1.59  res_preprocessed:                       163
% 7.00/1.59  prep_upred:                             0
% 7.00/1.59  prep_unflattend:                        26
% 7.00/1.59  smt_new_axioms:                         0
% 7.00/1.59  pred_elim_cands:                        7
% 7.00/1.59  pred_elim:                              1
% 7.00/1.59  pred_elim_cl:                           2
% 7.00/1.59  pred_elim_cycles:                       5
% 7.00/1.59  merged_defs:                            8
% 7.00/1.59  merged_defs_ncl:                        0
% 7.00/1.59  bin_hyper_res:                          8
% 7.00/1.59  prep_cycles:                            4
% 7.00/1.59  pred_elim_time:                         0.006
% 7.00/1.59  splitting_time:                         0.
% 7.00/1.59  sem_filter_time:                        0.
% 7.00/1.59  monotx_time:                            0.
% 7.00/1.59  subtype_inf_time:                       0.
% 7.00/1.59  
% 7.00/1.59  ------ Problem properties
% 7.00/1.59  
% 7.00/1.59  clauses:                                32
% 7.00/1.59  conjectures:                            13
% 7.00/1.59  epr:                                    12
% 7.00/1.59  horn:                                   23
% 7.00/1.59  ground:                                 15
% 7.00/1.59  unary:                                  14
% 7.00/1.59  binary:                                 8
% 7.00/1.59  lits:                                   126
% 7.00/1.59  lits_eq:                                14
% 7.00/1.59  fd_pure:                                0
% 7.00/1.59  fd_pseudo:                              0
% 7.00/1.59  fd_cond:                                0
% 7.00/1.59  fd_pseudo_cond:                         0
% 7.00/1.59  ac_symbols:                             0
% 7.00/1.59  
% 7.00/1.59  ------ Propositional Solver
% 7.00/1.59  
% 7.00/1.59  prop_solver_calls:                      28
% 7.00/1.59  prop_fast_solver_calls:                 3687
% 7.00/1.59  smt_solver_calls:                       0
% 7.00/1.59  smt_fast_solver_calls:                  0
% 7.00/1.59  prop_num_of_clauses:                    7216
% 7.00/1.59  prop_preprocess_simplified:             13404
% 7.00/1.59  prop_fo_subsumed:                       306
% 7.00/1.59  prop_solver_time:                       0.
% 7.00/1.59  smt_solver_time:                        0.
% 7.00/1.59  smt_fast_solver_time:                   0.
% 7.00/1.59  prop_fast_solver_time:                  0.
% 7.00/1.59  prop_unsat_core_time:                   0.
% 7.00/1.59  
% 7.00/1.59  ------ QBF
% 7.00/1.59  
% 7.00/1.59  qbf_q_res:                              0
% 7.00/1.59  qbf_num_tautologies:                    0
% 7.00/1.59  qbf_prep_cycles:                        0
% 7.00/1.59  
% 7.00/1.59  ------ BMC1
% 7.00/1.59  
% 7.00/1.59  bmc1_current_bound:                     -1
% 7.00/1.59  bmc1_last_solved_bound:                 -1
% 7.00/1.59  bmc1_unsat_core_size:                   -1
% 7.00/1.59  bmc1_unsat_core_parents_size:           -1
% 7.00/1.59  bmc1_merge_next_fun:                    0
% 7.00/1.59  bmc1_unsat_core_clauses_time:           0.
% 7.00/1.59  
% 7.00/1.59  ------ Instantiation
% 7.00/1.59  
% 7.00/1.59  inst_num_of_clauses:                    1580
% 7.00/1.59  inst_num_in_passive:                    45
% 7.00/1.59  inst_num_in_active:                     847
% 7.00/1.59  inst_num_in_unprocessed:                688
% 7.00/1.59  inst_num_of_loops:                      950
% 7.00/1.59  inst_num_of_learning_restarts:          0
% 7.00/1.59  inst_num_moves_active_passive:          100
% 7.00/1.59  inst_lit_activity:                      0
% 7.00/1.59  inst_lit_activity_moves:                1
% 7.00/1.59  inst_num_tautologies:                   0
% 7.00/1.59  inst_num_prop_implied:                  0
% 7.00/1.59  inst_num_existing_simplified:           0
% 7.00/1.59  inst_num_eq_res_simplified:             0
% 7.00/1.59  inst_num_child_elim:                    0
% 7.00/1.59  inst_num_of_dismatching_blockings:      186
% 7.00/1.59  inst_num_of_non_proper_insts:           1149
% 7.00/1.59  inst_num_of_duplicates:                 0
% 7.00/1.59  inst_inst_num_from_inst_to_res:         0
% 7.00/1.59  inst_dismatching_checking_time:         0.
% 7.00/1.59  
% 7.00/1.59  ------ Resolution
% 7.00/1.59  
% 7.00/1.59  res_num_of_clauses:                     0
% 7.00/1.59  res_num_in_passive:                     0
% 7.00/1.59  res_num_in_active:                      0
% 7.00/1.59  res_num_of_loops:                       167
% 7.00/1.59  res_forward_subset_subsumed:            35
% 7.00/1.59  res_backward_subset_subsumed:           0
% 7.00/1.59  res_forward_subsumed:                   0
% 7.00/1.59  res_backward_subsumed:                  0
% 7.00/1.59  res_forward_subsumption_resolution:     0
% 7.00/1.59  res_backward_subsumption_resolution:    0
% 7.00/1.59  res_clause_to_clause_subsumption:       2321
% 7.00/1.59  res_orphan_elimination:                 0
% 7.00/1.59  res_tautology_del:                      43
% 7.00/1.59  res_num_eq_res_simplified:              0
% 7.00/1.59  res_num_sel_changes:                    0
% 7.00/1.59  res_moves_from_active_to_pass:          0
% 7.00/1.59  
% 7.00/1.59  ------ Superposition
% 7.00/1.59  
% 7.00/1.59  sup_time_total:                         0.
% 7.00/1.59  sup_time_generating:                    0.
% 7.00/1.59  sup_time_sim_full:                      0.
% 7.00/1.59  sup_time_sim_immed:                     0.
% 7.00/1.59  
% 7.00/1.59  sup_num_of_clauses:                     307
% 7.00/1.59  sup_num_in_active:                      185
% 7.00/1.59  sup_num_in_passive:                     122
% 7.00/1.59  sup_num_of_loops:                       188
% 7.00/1.59  sup_fw_superposition:                   277
% 7.00/1.59  sup_bw_superposition:                   105
% 7.00/1.59  sup_immediate_simplified:               185
% 7.00/1.59  sup_given_eliminated:                   0
% 7.00/1.59  comparisons_done:                       0
% 7.00/1.59  comparisons_avoided:                    0
% 7.00/1.59  
% 7.00/1.59  ------ Simplifications
% 7.00/1.59  
% 7.00/1.59  
% 7.00/1.59  sim_fw_subset_subsumed:                 30
% 7.00/1.59  sim_bw_subset_subsumed:                 3
% 7.00/1.59  sim_fw_subsumed:                        17
% 7.00/1.59  sim_bw_subsumed:                        8
% 7.00/1.59  sim_fw_subsumption_res:                 7
% 7.00/1.59  sim_bw_subsumption_res:                 0
% 7.00/1.59  sim_tautology_del:                      1
% 7.00/1.59  sim_eq_tautology_del:                   13
% 7.00/1.59  sim_eq_res_simp:                        13
% 7.00/1.59  sim_fw_demodulated:                     78
% 7.00/1.59  sim_bw_demodulated:                     4
% 7.00/1.59  sim_light_normalised:                   87
% 7.00/1.59  sim_joinable_taut:                      0
% 7.00/1.59  sim_joinable_simp:                      0
% 7.00/1.59  sim_ac_normalised:                      0
% 7.00/1.59  sim_smt_subsumption:                    0
% 7.00/1.59  
%------------------------------------------------------------------------------
